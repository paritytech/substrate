// Copyright Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Helper for handling (i.e. answering) grandpa warp sync requests from a remote peer.

use codec::Decode;
use futures::{channel::oneshot, stream::StreamExt};
use log::debug;

use sc_network::{
	config::ProtocolId,
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
};
use sc_network_common::sync::warp::{EncodedProof, WarpProofRequest, WarpSyncProvider};
use sp_runtime::traits::Block as BlockT;

use std::{sync::Arc, time::Duration};

const MAX_RESPONSE_SIZE: u64 = 16 * 1024 * 1024;

/// Incoming warp requests bounded queue size.
const MAX_WARP_REQUEST_QUEUE: usize = 20;

/// Generates a [`RequestResponseConfig`] for the grandpa warp sync request protocol, refusing
/// incoming requests.
pub fn generate_request_response_config<Hash: AsRef<[u8]>>(
	protocol_id: ProtocolId,
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> RequestResponseConfig {
	RequestResponseConfig {
		name: generate_protocol_name(genesis_hash, fork_id).into(),
		fallback_names: std::iter::once(generate_legacy_protocol_name(protocol_id).into())
			.collect(),
		max_request_size: 32,
		max_response_size: MAX_RESPONSE_SIZE,
		request_timeout: Duration::from_secs(10),
		inbound_queue: None,
	}
}

/// Generate the grandpa warp sync protocol name from the genesi hash and fork id.
fn generate_protocol_name<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> String {
	let genesis_hash = genesis_hash.as_ref();
	if let Some(fork_id) = fork_id {
		format!("/{}/{}/sync/warp", array_bytes::bytes2hex("", genesis_hash), fork_id)
	} else {
		format!("/{}/sync/warp", array_bytes::bytes2hex("", genesis_hash))
	}
}

/// Generate the legacy grandpa warp sync protocol name from chain specific protocol identifier.
fn generate_legacy_protocol_name(protocol_id: ProtocolId) -> String {
	format!("/{}/sync/warp", protocol_id.as_ref())
}

/// Handler for incoming grandpa warp sync requests from a remote peer.
pub struct RequestHandler<TBlock: BlockT> {
	backend: Arc<dyn WarpSyncProvider<TBlock>>,
	request_receiver: async_channel::Receiver<IncomingRequest>,
}

impl<TBlock: BlockT> RequestHandler<TBlock> {
	/// Create a new [`RequestHandler`].
	pub fn new<Hash: AsRef<[u8]>>(
		protocol_id: ProtocolId,
		genesis_hash: Hash,
		fork_id: Option<&str>,
		backend: Arc<dyn WarpSyncProvider<TBlock>>,
	) -> (Self, RequestResponseConfig) {
		let (tx, request_receiver) = async_channel::bounded(MAX_WARP_REQUEST_QUEUE);

		let mut request_response_config =
			generate_request_response_config(protocol_id, genesis_hash, fork_id);
		request_response_config.inbound_queue = Some(tx);

		(Self { backend, request_receiver }, request_response_config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<OutgoingResponse>,
	) -> Result<(), HandleRequestError> {
		let request = WarpProofRequest::<TBlock>::decode(&mut &payload[..])?;

		let EncodedProof(proof) = self
			.backend
			.generate(request.begin)
			.map_err(HandleRequestError::InvalidRequest)?;

		pending_response
			.send(OutgoingResponse {
				result: Ok(proof),
				reputation_changes: Vec::new(),
				sent_feedback: None,
			})
			.map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`RequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(payload, pending_response) {
				Ok(()) => {
					debug!(target: "sync", "Handled grandpa warp sync request from {}.", peer)
				},
				Err(e) => debug!(
					target: "sync",
					"Failed to handle grandpa warp sync request from {}: {}",
					peer, e,
				),
			}
		}
	}
}

#[derive(Debug, thiserror::Error)]
enum HandleRequestError {
	#[error("Failed to decode request: {0}.")]
	DecodeProto(#[from] prost::DecodeError),

	#[error("Failed to encode response: {0}.")]
	EncodeProto(#[from] prost::EncodeError),

	#[error("Failed to decode block hash: {0}.")]
	DecodeScale(#[from] codec::Error),

	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	#[error("Invalid request {0}.")]
	InvalidRequest(#[from] Box<dyn std::error::Error + Send + Sync>),

	#[error("Failed to send response.")]
	SendResponse,
}
