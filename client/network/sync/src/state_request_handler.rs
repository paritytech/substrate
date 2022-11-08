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

//! Helper for handling (i.e. answering) state requests from a remote peer via the
//! `crate::request_responses::RequestResponsesBehaviour`.

use crate::schema::v1::{KeyValueStateEntry, StateEntry, StateRequest, StateResponse};
use codec::{Decode, Encode};
use futures::{
	channel::{mpsc, oneshot},
	stream::StreamExt,
};
use libp2p::PeerId;
use log::{debug, trace};
use lru::LruCache;
use prost::Message;
use sc_client_api::{BlockBackend, ProofProvider};
use sc_network_common::{
	config::ProtocolId,
	request_responses::{IncomingRequest, OutgoingResponse, ProtocolConfig},
};
use sp_runtime::traits::Block as BlockT;
use std::{
	hash::{Hash, Hasher},
	sync::Arc,
	time::Duration,
};

const LOG_TARGET: &str = "sync";
const MAX_RESPONSE_BYTES: usize = 2 * 1024 * 1024; // Actual reponse may be bigger.
const MAX_NUMBER_OF_SAME_REQUESTS_PER_PEER: usize = 2;

mod rep {
	use sc_peerset::ReputationChange as Rep;

	/// Reputation change when a peer sent us the same request multiple times.
	pub const SAME_REQUEST: Rep = Rep::new(i32::MIN, "Same state request multiple times");
}

/// Generates a [`ProtocolConfig`] for the state request protocol, refusing incoming requests.
pub fn generate_protocol_config<Hash: AsRef<[u8]>>(
	protocol_id: &ProtocolId,
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> ProtocolConfig {
	ProtocolConfig {
		name: generate_protocol_name(genesis_hash, fork_id).into(),
		fallback_names: std::iter::once(generate_legacy_protocol_name(protocol_id).into())
			.collect(),
		max_request_size: 1024 * 1024,
		max_response_size: 16 * 1024 * 1024,
		request_timeout: Duration::from_secs(40),
		inbound_queue: None,
	}
}

/// Generate the state protocol name from the genesis hash and fork id.
fn generate_protocol_name<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> String {
	let genesis_hash = genesis_hash.as_ref();
	if let Some(fork_id) = fork_id {
		format!("/{}/{}/state/2", array_bytes::bytes2hex("", genesis_hash), fork_id)
	} else {
		format!("/{}/state/2", array_bytes::bytes2hex("", genesis_hash))
	}
}

/// Generate the legacy state protocol name from chain specific protocol identifier.
fn generate_legacy_protocol_name(protocol_id: &ProtocolId) -> String {
	format!("/{}/state/2", protocol_id.as_ref())
}

/// The key of [`BlockRequestHandler::seen_requests`].
#[derive(Eq, PartialEq, Clone)]
struct SeenRequestsKey<B: BlockT> {
	peer: PeerId,
	block: B::Hash,
	start: Vec<Vec<u8>>,
}

#[allow(clippy::derive_hash_xor_eq)]
impl<B: BlockT> Hash for SeenRequestsKey<B> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.peer.hash(state);
		self.block.hash(state);
		self.start.hash(state);
	}
}

/// The value of [`StateRequestHandler::seen_requests`].
enum SeenRequestsValue {
	/// First time we have seen the request.
	First,
	/// We have fulfilled the request `n` times.
	Fulfilled(usize),
}

/// Handler for incoming block requests from a remote peer.
pub struct StateRequestHandler<B: BlockT, Client> {
	client: Arc<Client>,
	request_receiver: mpsc::Receiver<IncomingRequest>,
	/// Maps from request to number of times we have seen this request.
	///
	/// This is used to check if a peer is spamming us with the same request.
	seen_requests: LruCache<SeenRequestsKey<B>, SeenRequestsValue>,
}

impl<B, Client> StateRequestHandler<B, Client>
where
	B: BlockT,
	Client: BlockBackend<B> + ProofProvider<B> + Send + Sync + 'static,
{
	/// Create a new [`StateRequestHandler`].
	pub fn new(
		protocol_id: &ProtocolId,
		fork_id: Option<&str>,
		client: Arc<Client>,
		num_peer_hint: usize,
	) -> (Self, ProtocolConfig) {
		// Reserve enough request slots for one request per peer when we are at the maximum
		// number of peers.
		let (tx, request_receiver) = mpsc::channel(num_peer_hint);

		let mut protocol_config = generate_protocol_config(
			protocol_id,
			client
				.block_hash(0u32.into())
				.ok()
				.flatten()
				.expect("Genesis block exists; qed"),
			fork_id,
		);
		protocol_config.inbound_queue = Some(tx);

		let seen_requests = LruCache::new(num_peer_hint * 2);

		(Self { client, request_receiver, seen_requests }, protocol_config)
	}

	/// Run [`StateRequestHandler`].
	pub async fn run(mut self) {
		while let Some(request) = self.request_receiver.next().await {
			let IncomingRequest { peer, payload, pending_response } = request;

			match self.handle_request(payload, pending_response, &peer) {
				Ok(()) => debug!(target: LOG_TARGET, "Handled block request from {}.", peer),
				Err(e) => debug!(
					target: LOG_TARGET,
					"Failed to handle state request from {}: {}", peer, e,
				),
			}
		}
	}

	fn handle_request(
		&mut self,
		payload: Vec<u8>,
		pending_response: oneshot::Sender<OutgoingResponse>,
		peer: &PeerId,
	) -> Result<(), HandleRequestError> {
		let request = StateRequest::decode(&payload[..])?;
		let block: B::Hash = Decode::decode(&mut request.block.as_ref())?;

		let key = SeenRequestsKey { peer: *peer, block, start: request.start.clone() };

		let mut reputation_changes = Vec::new();

		match self.seen_requests.get_mut(&key) {
			Some(SeenRequestsValue::First) => {},
			Some(SeenRequestsValue::Fulfilled(ref mut requests)) => {
				*requests = requests.saturating_add(1);

				if *requests > MAX_NUMBER_OF_SAME_REQUESTS_PER_PEER {
					reputation_changes.push(rep::SAME_REQUEST);
				}
			},
			None => {
				self.seen_requests.put(key.clone(), SeenRequestsValue::First);
			},
		}

		trace!(
			target: LOG_TARGET,
			"Handling state request from {}: Block {:?}, Starting at {:x?}, no_proof={}",
			peer,
			request.block,
			&request.start,
			request.no_proof,
		);

		let result = if reputation_changes.is_empty() {
			let mut response = StateResponse::default();

			if !request.no_proof {
				let (proof, _count) = self.client.read_proof_collection(
					block,
					request.start.as_slice(),
					MAX_RESPONSE_BYTES,
				)?;
				response.proof = proof.encode();
			} else {
				let entries = self.client.storage_collection(
					block,
					request.start.as_slice(),
					MAX_RESPONSE_BYTES,
				)?;
				response.entries = entries
					.into_iter()
					.map(|(state, complete)| KeyValueStateEntry {
						state_root: state.state_root,
						entries: state
							.key_values
							.into_iter()
							.map(|(key, value)| StateEntry { key, value })
							.collect(),
						complete,
					})
					.collect();
			}

			trace!(
				target: LOG_TARGET,
				"StateResponse contains {} keys, {}, proof nodes, from {:?} to {:?}",
				response.entries.len(),
				response.proof.len(),
				response.entries.get(0).and_then(|top| top
					.entries
					.first()
					.map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key))),
				response.entries.get(0).and_then(|top| top
					.entries
					.last()
					.map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key))),
			);
			if let Some(value) = self.seen_requests.get_mut(&key) {
				// If this is the first time we have processed this request, we need to change
				// it to `Fulfilled`.
				if let SeenRequestsValue::First = value {
					*value = SeenRequestsValue::Fulfilled(1);
				}
			}

			let mut data = Vec::with_capacity(response.encoded_len());
			response.encode(&mut data)?;
			Ok(data)
		} else {
			Err(())
		};

		pending_response
			.send(OutgoingResponse { result, reputation_changes, sent_feedback: None })
			.map_err(|_| HandleRequestError::SendResponse)
	}
}

#[derive(Debug, thiserror::Error)]
enum HandleRequestError {
	#[error("Failed to decode request: {0}.")]
	DecodeProto(#[from] prost::DecodeError),

	#[error("Failed to encode response: {0}.")]
	EncodeProto(#[from] prost::EncodeError),

	#[error("Failed to decode block hash: {0}.")]
	InvalidHash(#[from] codec::Error),

	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	#[error("Failed to send response.")]
	SendResponse,
}
