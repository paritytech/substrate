// Copyright 2021 Parity Technologies (UK) Ltd.
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
use sc_network::config::{IncomingRequest, OutgoingResponse, ProtocolId, RequestResponseConfig};
use sc_client_api::Backend;
use sp_runtime::traits::NumberFor;
use futures::channel::{mpsc, oneshot};
use futures::stream::StreamExt;
use log::debug;
use sp_runtime::traits::Block as BlockT;
use std::time::Duration;
use std::sync::Arc;
use sc_service::{SpawnTaskHandle, config::{Configuration, Role}};
use sc_finality_grandpa::WarpSyncFragmentCache;

/// Generates the appropriate [`RequestResponseConfig`] for a given chain configuration.
pub fn request_response_config_for_chain<TBlock: BlockT, TBackend: Backend<TBlock> + 'static>(
	config: &Configuration,
	spawn_handle: SpawnTaskHandle,
	backend: Arc<TBackend>,
) -> RequestResponseConfig
	where NumberFor<TBlock>: sc_finality_grandpa::BlockNumberOps,
{
	let protocol_id = config.protocol_id();

	if matches!(config.role, Role::Light) {
		// Allow outgoing requests but deny incoming requests.
		generate_request_response_config(protocol_id.clone())
	} else {
		// Allow both outgoing and incoming requests.
		let (handler, request_response_config) = GrandpaWarpSyncRequestHandler::new(
			protocol_id.clone(),
			backend.clone(),
		);
		spawn_handle.spawn("grandpa_warp_sync_request_handler", handler.run());
		request_response_config
	}
}

const LOG_TARGET: &str = "finality-grandpa-warp-sync-request-handler";

/// Generates a [`RequestResponseConfig`] for the grandpa warp sync request protocol, refusing incoming requests.
pub fn generate_request_response_config(protocol_id: ProtocolId) -> RequestResponseConfig {
	RequestResponseConfig {
		name: generate_protocol_name(protocol_id).into(),
		max_request_size: 32,
		max_response_size: 16 * 1024 * 1024,
		request_timeout: Duration::from_secs(10),
		inbound_queue: None,
	}
}

/// Generate the grandpa warp sync protocol name from chain specific protocol identifier.
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

/// Setting a large fragment limit, allowing client
/// to define it is possible.
const WARP_SYNC_FRAGMENTS_LIMIT: usize = 100;

/// Number of item with justification in warp sync cache.
/// This should be customizable, but setting it to the max number of fragments
/// we return seems like a good idea until then.
const WARP_SYNC_CACHE_SIZE: usize = WARP_SYNC_FRAGMENTS_LIMIT;

/// Handler for incoming grandpa warp sync requests from a remote peer.
pub struct GrandpaWarpSyncRequestHandler<TBackend, TBlock: BlockT> {
	backend: Arc<TBackend>,
	cache: Arc<parking_lot::RwLock<WarpSyncFragmentCache<TBlock::Header>>>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
	_phantom: std::marker::PhantomData<TBlock>
}

impl<TBlock: BlockT, TBackend: Backend<TBlock>> GrandpaWarpSyncRequestHandler<TBackend, TBlock> {
	/// Create a new [`GrandpaWarpSyncRequestHandler`].
	pub fn new(protocol_id: ProtocolId, backend: Arc<TBackend>) -> (Self, RequestResponseConfig) {
		let (tx, request_receiver) = mpsc::channel(20);

		let mut request_response_config = generate_request_response_config(protocol_id);
		request_response_config.inbound_queue = Some(tx);
		let cache = Arc::new(parking_lot::RwLock::new(WarpSyncFragmentCache::new(WARP_SYNC_CACHE_SIZE)));

		(Self { backend, request_receiver, cache, _phantom: std::marker::PhantomData }, request_response_config)
	}

	fn handle_request(
		&self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<OutgoingResponse>
	) -> Result<(), HandleRequestError>
		where NumberFor<TBlock>: sc_finality_grandpa::BlockNumberOps,
	{
		let request = Request::<TBlock>::decode(&mut &payload[..])?;

		let mut cache = self.cache.write();
		let response = sc_finality_grandpa::prove_warp_sync(
			self.backend.blockchain(), request.begin, Some(WARP_SYNC_FRAGMENTS_LIMIT), Some(&mut cache)
		)?;

		pending_response.send(OutgoingResponse {
			result: Ok(response),
			reputation_changes: Vec::new(),
		}).map_err(|_| HandleRequestError::SendResponse)
	}

	/// Run [`GrandpaWarpSyncRequestHandler`].
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
