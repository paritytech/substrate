// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Helper for handling (i.e. answering) grandpa warp sync requests from a remote peer via the
//! [`crate::request_responses::RequestResponsesBehaviour`].

use codec::Decode;
use sc_network::config::ProtocolId;
use sc_network::request_responses::{IncomingRequest, ProtocolConfig};
use sc_client_api::Backend;
use sc_finality_grandpa::GrandpaJustification;
use sp_runtime::traits::NumberFor;
use futures::channel::{mpsc, oneshot};
use futures::stream::StreamExt;
use log::debug;
use sp_runtime::traits::Block as BlockT;
use std::time::Duration;
use std::sync::Arc;

const LOG_TARGET: &str = "grandpa-warp-sync-request-handler";

/// Generates a [`ProtocolConfig`] for the block request protocol, refusing incoming requests.
pub fn generate_protocol_config(protocol_id: ProtocolId) -> ProtocolConfig {
	ProtocolConfig {
		name: generate_protocol_name(protocol_id).into(),
		// todo
		max_request_size: 1024 * 1024,
		// todo
		max_response_size: 16 * 1024 * 1024,
		request_timeout: Duration::from_secs(40),
		inbound_queue: None,
	}
}

/// Generate the block protocol name from chain specific protocol identifier.
fn generate_protocol_name(protocol_id: ProtocolId) -> String {
	let mut s = String::new();
	s.push_str("/");
	s.push_str(protocol_id.as_ref());
	s.push_str("/sync/warp");
	s
}

#[derive(codec::Decode)]
struct Request<B: BlockT> {
	begin: B::Hash
}

/// Handler for incoming block requests from a remote peer.
pub struct GrandpaWarpSyncRequestHandler<TBackend, TBlock> {
	backend: Arc<TBackend>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
	_phantom: std::marker::PhantomData<TBlock>
}

impl<TBlock: BlockT, TBackend: Backend<TBlock>> GrandpaWarpSyncRequestHandler<TBackend, TBlock> {
	/// Create a new [`BlockRequestHandler`].
	pub fn new(protocol_id: ProtocolId, backend: Arc<TBackend>) -> (Self, ProtocolConfig) {
		// Rate of arrival multiplied with the waiting time in the queue equals the queue length.
		//
		// An average Polkadot sentry node serves less than 5 requests per second. The 95th percentile
		// serving a request is less than 2 second. Thus one would estimate the queue length to be
		// below 10.
		//
		// Choosing 20 as the queue length to give some additional buffer.
		let (tx, request_receiver) = mpsc::channel(20);

		let mut protocol_config = generate_protocol_config(protocol_id);
		protocol_config.inbound_queue = Some(tx);

		(Self { backend, request_receiver, _phantom: std::marker::PhantomData }, protocol_config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<Vec<u8>>
	) -> Result<(), HandleRequestError>
		where NumberFor<TBlock>: sc_finality_grandpa::BlockNumberOps,
	{
		let request = Request::<TBlock>::decode(&mut &payload[..])?;

		let response = sc_finality_grandpa::finality_proof::prove_authority::<_, _, GrandpaJustification<TBlock>>(
			self.backend.blockchain(), request.begin,
		)?;

		pending_response.send(response)
			.map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`BlockRequestHandler`].
	pub async fn run(mut self)
		where NumberFor<TBlock>: sc_finality_grandpa::BlockNumberOps,
	{
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(payload, pending_response) {
				Ok(()) => debug!(target: LOG_TARGET, "Handled grandpa warp sync request from {}.", peer),
				Err(e) => debug!(
					target: LOG_TARGET,
					"Failed to handle grandpa warp sync request from {}: {}",
					peer, e,
				),
			}
		}
	}
}

#[derive(derive_more::Display, derive_more::From)]
enum HandleRequestError {
	#[display(fmt = "Failed to decode request: {}.", _0)]
	DecodeProto(prost::DecodeError),
	#[display(fmt = "Failed to encode response: {}.", _0)]
	EncodeProto(prost::EncodeError),
	#[display(fmt = "Failed to decode block hash: {}.", _0)]
	DecodeScale(codec::Error),
	Client(sp_blockchain::Error),
	#[display(fmt = "Failed to send response.")]
	SendResponse,
}
