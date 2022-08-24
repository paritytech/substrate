// Copyright 2022 Parity Technologies (UK) Ltd.
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

//! Helper for handling (i.e. answering) BEEFY justifications requests from a remote peer.

use codec::Decode;
use futures::{
	channel::{mpsc, oneshot},
	stream::StreamExt,
};
use log::debug;
use sc_client_api::BlockBackend;
use sc_network_common::{
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	sync::beefy::{BeefyJustifRequest, BEEFY_LOG_TARGET},
};
use sp_runtime::{generic::BlockId, traits::Block};
use std::{marker::PhantomData, sync::Arc, time::Duration};

// TODO: use better value here
const MAX_RESPONSE_SIZE: u64 = 1024 * 1024;

// TODO: use the definition from primitives
const BEEFY_ENGINE_ID: sp_runtime::ConsensusEngineId = *b"BEEF";

/// Generates a [`RequestResponseConfig`] for the BEEFY justifications request protocol,
/// refusing incoming requests (incoming requests will be initialized later).
pub fn generate_request_response_config<Hash: AsRef<[u8]>>(
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> RequestResponseConfig {
	RequestResponseConfig {
		name: generate_protocol_name(genesis_hash, fork_id).into(),
		fallback_names: vec![],
		// TODO: use better value here
		max_request_size: 32,
		max_response_size: MAX_RESPONSE_SIZE,
		request_timeout: Duration::from_secs(10),
		inbound_queue: None,
	}
}

/// Generate the name of the BEEFY justifications request-response protocol.
fn generate_protocol_name<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> String {
	if let Some(fork_id) = fork_id {
		format!("/{}/{}/beefy/justifications/1", hex::encode(genesis_hash), fork_id)
	} else {
		format!("/{}/beefy/justifications/1", hex::encode(genesis_hash))
	}
}

/// Handler for incoming BEEFY justifications requests from a remote peer.
pub struct BeefyJustifsRequestHandler<B, Client> {
	request_receiver: mpsc::Receiver<IncomingRequest>,
	/// Blockchain client.
	client: Arc<Client>,
	_block: PhantomData<B>,
}

impl<B, Client> BeefyJustifsRequestHandler<B, Client>
where
	B: Block,
	Client: BlockBackend<B> + Send + Sync + 'static,
{
	/// Create a new [`BeefyJustifsRequestHandler`].
	pub fn new(fork_id: Option<&str>, client: Arc<Client>) -> (Self, RequestResponseConfig) {
		let (tx, request_receiver) = mpsc::channel(20);

		let genesis_hash = client
			.block_hash(0u32.into())
			.ok()
			.flatten()
			.expect("Genesis block exists; qed");
		let mut config = generate_request_response_config(genesis_hash, fork_id);
		config.inbound_queue = Some(tx);

		(Self { client, request_receiver, _block: PhantomData }, config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<OutgoingResponse>,
	) -> Result<(), HandleRequestError> {
		let request = BeefyJustifRequest::<B>::decode(&mut &payload[..])?;
		// TODO: validate `request.begin` and change peer reputation for invalid requests.

		let proof = self
			.client
			.justifications(&BlockId::Number(request.begin))
			.map_err(HandleRequestError::Client)?
			.map(|justifs| justifs.get(BEEFY_ENGINE_ID).cloned())
			.flatten()
			// No BEEFY justification present.
			.ok_or(());

		pending_response
			.send(OutgoingResponse {
				result: proof,
				reputation_changes: Vec::new(),
				sent_feedback: None,
			})
			.map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`BeefyJustifsRequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;
			match self.handle_request(payload, pending_response) {
				Ok(()) => {
					debug!(
						target: BEEFY_LOG_TARGET,
						"Handled BEEFY justification request from {}.", peer
					)
				},
				Err(e) => {
					// TODO: handle reputation changes here

					debug!(
						target: BEEFY_LOG_TARGET,
						"Failed to handle BEEFY justification request from {}: {}", peer, e,
					)
				},
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
