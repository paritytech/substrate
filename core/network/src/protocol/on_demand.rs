// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! On-demand requests service.

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Instant, Duration};
use log::{trace, info};
use futures::sync::oneshot::{Sender as OneShotSender};
use linked_hash_map::{Entry, LinkedHashMap};
use client::error::Error as ClientError;
use client::light::fetcher::{FetchChecker, RemoteHeaderRequest,
	RemoteCallRequest, RemoteReadRequest, RemoteChangesRequest, ChangesProof,
	RemoteReadChildRequest, RemoteBodyRequest};
use crate::message::{self, BlockAttributes, Direction, FromBlock, RequestId};
use network_libp2p::PeerId;
use crate::config::Roles;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor};

/// Remote request timeout.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(15);
/// Default request retry count.
const RETRY_COUNT: usize = 1;
/// Reputation change for a peer when a request timed out.
const TIMEOUT_REPUTATION_CHANGE: i32 = -(1 << 8);

/// Trait used by the `OnDemandCore` service to communicate messages back to the network.
pub trait OnDemandNetwork<B: BlockT> {
	/// Adjusts the reputation of the given peer.
	fn report_peer(&mut self, who: &PeerId, reputation_change: i32);

	/// Disconnect from the given peer. Used in case of misbehaviour.
	fn disconnect_peer(&mut self, who: &PeerId);

	/// Send to `who` a request for a header.
	fn send_header_request(&mut self, who: &PeerId, id: RequestId, block: <<B as BlockT>::Header as HeaderT>::Number);

	/// Send to `who` a read request.
	fn send_read_request(&mut self, who: &PeerId, id: RequestId, block: <B as BlockT>::Hash, key: Vec<u8>);

	/// Send to `who` a child read request.
	fn send_read_child_request(
		&mut self,
		who: &PeerId,
		id: RequestId,
		block: <B as BlockT>::Hash,
		storage_key: Vec<u8>,
		key: Vec<u8>
	);

	/// Send to `who` a call request.
	fn send_call_request(
		&mut self,
		who: &PeerId,
		id: RequestId,
		block: <B as BlockT>::Hash,
		method: String,
		data: Vec<u8>
	);

	/// Send to `who` a changes request.
	fn send_changes_request(
		&mut self,
		who: &PeerId,
		id: RequestId,
		first: <B as BlockT>::Hash,
		last: <B as BlockT>::Hash,
		min: <B as BlockT>::Hash,
		max: <B as BlockT>::Hash,
		key: Vec<u8>
	);

	/// Send to `who` a body request.
	fn send_body_request(
		&mut self,
		who: &PeerId,
		id: RequestId,
		fields: BlockAttributes,
		from: FromBlock<<B as BlockT>::Hash, <<B as BlockT>::Header as HeaderT>::Number>,
		to: Option<B::Hash>,
		direction: Direction,
		max: Option<u32>
	);
}

/// On-demand requests service. Dispatches requests to appropriate peers.
pub struct OnDemandCore<B: BlockT> {
	checker: Arc<dyn FetchChecker<B>>,
	next_request_id: u64,
	pending_requests: VecDeque<Request<B>>,
	active_peers: LinkedHashMap<PeerId, Request<B>>,
	idle_peers: VecDeque<PeerId>,
	best_blocks: HashMap<PeerId, NumberFor<B>>,
}

struct Request<Block: BlockT> {
	id: u64,
	timestamp: Instant,
	retry_count: usize,
	data: RequestData<Block>,
}

/// One request for data made by the `Client`.
///
/// Contains a `Sender` where to send the result.
pub(crate) enum RequestData<Block: BlockT> {
	RemoteBody(RemoteBodyRequest<Block::Header>, OneShotSender<Result<Vec<Block::Extrinsic>, ClientError>>),
	RemoteHeader(RemoteHeaderRequest<Block::Header>, OneShotSender<Result<Block::Header, ClientError>>),
	RemoteRead(RemoteReadRequest<Block::Header>, OneShotSender<Result<Option<Vec<u8>>, ClientError>>),
	RemoteReadChild(
		RemoteReadChildRequest<Block::Header>,
		OneShotSender<Result<Option<Vec<u8>>, ClientError>>
	),
	RemoteCall(RemoteCallRequest<Block::Header>, OneShotSender<Result<Vec<u8>, ClientError>>),
	RemoteChanges(
		RemoteChangesRequest<Block::Header>,
		OneShotSender<Result<Vec<(NumberFor<Block>, u32)>, ClientError>>
	),
}

enum Accept<Block: BlockT> {
	Ok,
	CheckFailed(ClientError, RequestData<Block>),
	Unexpected(RequestData<Block>),
}

/// Dummy implementation of `FetchChecker` that always assumes that responses are bad.
///
/// Considering that it is the responsibility of the client to build the fetcher, it can use this
/// implementation if it knows that it will never perform any request.
#[derive(Default, Clone)]
pub struct AlwaysBadChecker;

impl<Block: BlockT> FetchChecker<Block> for AlwaysBadChecker {
	fn check_header_proof(
		&self,
		_request: &RemoteHeaderRequest<Block::Header>,
		_remote_header: Option<Block::Header>,
		_remote_proof: Vec<Vec<u8>>
	) -> Result<Block::Header, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_read_proof(
		&self,
		_request: &RemoteReadRequest<Block::Header>,
		_remote_proof: Vec<Vec<u8>>
	) -> Result<Option<Vec<u8>>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_read_child_proof(
		&self,
		_request: &RemoteReadChildRequest<Block::Header>,
		_remote_proof: Vec<Vec<u8>>
	) -> Result<Option<Vec<u8>>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_execution_proof(
		&self,
		_request: &RemoteCallRequest<Block::Header>,
		_remote_proof: Vec<Vec<u8>>
	) -> Result<Vec<u8>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_changes_proof(
		&self,
		_request: &RemoteChangesRequest<Block::Header>,
		_remote_proof: ChangesProof<Block::Header>
	) -> Result<Vec<(NumberFor<Block>, u32)>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}

	fn check_body_proof(
		&self,
		_request: &RemoteBodyRequest<Block::Header>,
		_body: Vec<Block::Extrinsic>
	) -> Result<Vec<Block::Extrinsic>, ClientError> {
		Err(ClientError::Msg("AlwaysBadChecker".into()))
	}
}

impl<B: BlockT> OnDemandCore<B> where
	B::Header: HeaderT,
{
	/// Creates new on-demand requests processer.
	pub fn new(checker: Arc<dyn FetchChecker<B>>) -> Self {
		OnDemandCore {
			checker,
			next_request_id: 0,
			pending_requests: VecDeque::new(),
			active_peers: LinkedHashMap::new(),
			idle_peers: VecDeque::new(),
			best_blocks: HashMap::new(),
		}
	}

	/// Inserts a new request in the list of requests to execute.
	pub(crate) fn add_request(&mut self, network: impl OnDemandNetwork<B>, data: RequestData<B>) {
		self.insert(RETRY_COUNT, data);
		self.dispatch(network);
	}

	/// Inserts a new request in the list of requests to execute.
	fn insert(&mut self, retry_count: usize, data: RequestData<B>) {
		let request_id = self.next_request_id;
		self.next_request_id += 1;

		self.pending_requests.push_back(Request {
			id: request_id,
			timestamp: Instant::now(),
			retry_count,
			data,
		});
	}

	/// Try to accept response from given peer.
	fn accept_response(
		&mut self,
		rtype: &str,
		mut network: impl OnDemandNetwork<B>,
		peer: PeerId,
		request_id: u64,
		try_accept: impl FnOnce(Request<B>, &Arc<dyn FetchChecker<B>>) -> Accept<B>
	) {
		let request = match self.remove(peer.clone(), request_id) {
			Some(request) => request,
			None => {
				info!("Invalid remote {} response from peer {}", rtype, peer);
				network.report_peer(&peer, i32::min_value());
				network.disconnect_peer(&peer);
				self.remove_peer(peer);
				return;
			},
		};

		let retry_count = request.retry_count;
		let (retry_count, retry_request_data) = match try_accept(request, &self.checker) {
			Accept::Ok => (retry_count, None),
			Accept::CheckFailed(error, retry_request_data) => {
				info!("Failed to check remote {} response from peer {}: {}", rtype, peer, error);
				network.report_peer(&peer, i32::min_value());
				network.disconnect_peer(&peer);
				self.remove_peer(peer);

				if retry_count > 0 {
					(retry_count - 1, Some(retry_request_data))
				} else {
					trace!(target: "sync", "Failed to get remote {} response for given number of retries", rtype);
					retry_request_data.fail(ClientError::RemoteFetchFailed.into());
					(0, None)
				}
			},
			Accept::Unexpected(retry_request_data) => {
				info!("Unexpected response to remote {} from peer", rtype);
				network.report_peer(&peer, i32::min_value());
				network.disconnect_peer(&peer);
				self.remove_peer(peer);

				(retry_count, Some(retry_request_data))
			},
		};

		if let Some(request_data) = retry_request_data {
			self.insert(retry_count, request_data);
		}

		self.dispatch(network);
	}

	pub fn on_connect(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		role: Roles,
		best_number: NumberFor<B>
	) {
		if !role.is_full() {
			return;
		}

		self.idle_peers.push_back(peer.clone());
		self.best_blocks.insert(peer, best_number);

		self.dispatch(network);
	}

	pub fn on_block_announce(&mut self, network: impl OnDemandNetwork<B>, peer: PeerId, best_number: NumberFor<B>) {
		self.best_blocks.insert(peer, best_number);
		self.dispatch(network);
	}

	pub fn on_disconnect(&mut self, network: impl OnDemandNetwork<B>, peer: PeerId) {
		self.remove_peer(peer);
		self.dispatch(network);
	}

	pub fn maintain_peers(&mut self, mut network: impl OnDemandNetwork<B>) {
		let now = Instant::now();

		loop {
			match self.active_peers.front() {
				Some((_, request)) if now - request.timestamp >= REQUEST_TIMEOUT => (),
				_ => break,
			}

			let (bad_peer, request) = self.active_peers.pop_front().expect("front() is Some as checked above");
			self.pending_requests.push_front(request);
			network.report_peer(&bad_peer, TIMEOUT_REPUTATION_CHANGE);
			network.disconnect_peer(&bad_peer);
		}

		self.dispatch(network);
	}

	pub fn on_remote_header_response(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		response: message::RemoteHeaderResponse<B::Header>
	) {
		self.accept_response("header", network, peer, response.id, |request, checker| match request.data {
			RequestData::RemoteHeader(request, sender) => match checker.check_header_proof(
				&request,
				response.header,
				response.proof
			) {
				Ok(response) => {
					// we do not bother if receiver has been dropped already
					let _ = sender.send(Ok(response));
					Accept::Ok
				},
				Err(error) => Accept::CheckFailed(error, RequestData::RemoteHeader(request, sender)),
			},
			data => Accept::Unexpected(data),
		})
	}

	pub fn on_remote_read_response(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		response: message::RemoteReadResponse
	) {
		self.accept_response("read", network, peer, response.id, |request, checker| match request.data {
			RequestData::RemoteRead(request, sender) => {
				match checker.check_read_proof(&request, response.proof) {
					Ok(response) => {
						// we do not bother if receiver has been dropped already
						let _ = sender.send(Ok(response));
						Accept::Ok
					},
					Err(error) => Accept::CheckFailed(
						error,
						RequestData::RemoteRead(request, sender)
					),
			}},
			RequestData::RemoteReadChild(request, sender) => {
				match checker.check_read_child_proof(&request, response.proof) {
					Ok(response) => {
						// we do not bother if receiver has been dropped already
						let _ = sender.send(Ok(response));
						Accept::Ok
					},
					Err(error) => Accept::CheckFailed(
						error,
						RequestData::RemoteReadChild(request, sender)
					),
			}},
			data => Accept::Unexpected(data),
		})
	}

	pub fn on_remote_call_response(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		response: message::RemoteCallResponse
	) {
		self.accept_response("call", network, peer, response.id, |request, checker| match request.data {
			RequestData::RemoteCall(request, sender) => match checker.check_execution_proof(&request, response.proof) {
				Ok(response) => {
					// we do not bother if receiver has been dropped already
					let _ = sender.send(Ok(response));
					Accept::Ok
				},
				Err(error) => Accept::CheckFailed(error, RequestData::RemoteCall(request, sender)),
			},
			data => Accept::Unexpected(data),
		})
	}

	pub fn on_remote_changes_response(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		response: message::RemoteChangesResponse<NumberFor<B>, B::Hash>
	) {
		self.accept_response("changes", network, peer, response.id, |request, checker| match request.data {
			RequestData::RemoteChanges(request, sender) => match checker.check_changes_proof(
				&request, ChangesProof {
					max_block: response.max,
					proof: response.proof,
					roots: response.roots.into_iter().collect(),
					roots_proof: response.roots_proof,
			}) {
				Ok(response) => {
					// we do not bother if receiver has been dropped already
					let _ = sender.send(Ok(response));
					Accept::Ok
				},
				Err(error) => Accept::CheckFailed(error, RequestData::RemoteChanges(request, sender)),
			},
			data => Accept::Unexpected(data),
		})
	}

	pub fn on_remote_body_response(
		&mut self,
		network: impl OnDemandNetwork<B>,
		peer: PeerId,
		response: message::BlockResponse<B>
	) {
		self.accept_response("body", network, peer, response.id, |request, checker| match request.data {
			RequestData::RemoteBody(request, sender) => {
				let mut bodies: Vec<_> = response
					.blocks
					.into_iter()
					.filter_map(|b| b.body)
					.collect();

				// Number of bodies are hardcoded to 1 for valid `RemoteBodyResponses`
				if bodies.len() != 1 {
					return Accept::CheckFailed(
						"RemoteBodyResponse: invalid number of blocks".into(),
						RequestData::RemoteBody(request, sender),
					)
				}
				let body = bodies.remove(0);

				match checker.check_body_proof(&request, body) {
					Ok(body) => {
						let _ = sender.send(Ok(body));
						Accept::Ok
					}
					Err(error) => Accept::CheckFailed(error, RequestData::RemoteBody(request, sender)),
				}
			}
			other => Accept::Unexpected(other),
		})
	}

	pub fn is_on_demand_response(&self, peer: &PeerId, request_id: message::RequestId) -> bool {
		self.active_peers.get(&peer).map_or(false, |r| r.id == request_id)
	}

	fn remove(&mut self, peer: PeerId, id: u64) -> Option<Request<B>> {
		match self.active_peers.entry(peer.clone()) {
			Entry::Occupied(entry) => match entry.get().id == id {
				true => {
					self.idle_peers.push_back(peer);
					Some(entry.remove())
				},
				false => None,
			},
			Entry::Vacant(_) => None,
		}
	}

	pub fn remove_peer(&mut self, peer: PeerId) {
		self.best_blocks.remove(&peer);

		if let Some(request) = self.active_peers.remove(&peer) {
			self.pending_requests.push_front(request);
			return;
		}

		if let Some(idle_index) = self.idle_peers.iter().position(|i| *i == peer) {
			self.idle_peers.swap_remove_back(idle_index);
		}
	}

	/// Dispatches pending requests.
	fn dispatch(&mut self, mut network: impl OnDemandNetwork<B>) {
		let mut last_peer = self.idle_peers.back().cloned();
		let mut unhandled_requests = VecDeque::new();

		loop {
			let peer = match self.idle_peers.pop_front() {
				Some(peer) => peer,
				None => break,
			};

			// check if request can (optimistically) be processed by the peer
			let can_be_processed_by_peer = {
				let request = match self.pending_requests.front() {
					Some(r) => r,
					None => {
						self.idle_peers.push_front(peer);
						break;
					},
				};
				let peer_best_block = self.best_blocks.get(&peer)
					.expect("entries are inserted into best_blocks when peer is connected;
						entries are removed from best_blocks when peer is disconnected;
						peer is in idle_peers and thus connected; qed");
				request.required_block() <= *peer_best_block
			};

			if !can_be_processed_by_peer {
				// return peer to the back of the queue
				self.idle_peers.push_back(peer.clone());

				// we have enumerated all peers and noone can handle request
				if Some(peer) == last_peer {
					let request = self.pending_requests.pop_front().expect("checked in loop condition; qed");
					unhandled_requests.push_back(request);
					last_peer = self.idle_peers.back().cloned();
				}

				continue;
			}

			last_peer = self.idle_peers.back().cloned();

			let mut request = self.pending_requests.pop_front().expect("checked in loop condition; qed");
			request.timestamp = Instant::now();
			trace!(target: "sync", "Dispatching remote request {} to peer {}", request.id, peer);
			request.send_to(&mut network, &peer);
			self.active_peers.insert(peer, request);
		}

		self.pending_requests.append(&mut unhandled_requests);
	}
}

impl<Block: BlockT> Request<Block> {
	fn required_block(&self) -> NumberFor<Block> {
		match self.data {
			RequestData::RemoteHeader(ref data, _) => data.block,
			RequestData::RemoteRead(ref data, _) => *data.header.number(),
			RequestData::RemoteReadChild(ref data, _) => *data.header.number(),
			RequestData::RemoteCall(ref data, _) => *data.header.number(),
			RequestData::RemoteChanges(ref data, _) => data.max_block.0,
			RequestData::RemoteBody(ref data, _) => *data.header.number(),
		}
	}

	fn send_to(&self, out: &mut impl OnDemandNetwork<Block>, peer: &PeerId) {
		match self.data {
			RequestData::RemoteHeader(ref data, _) =>
				out.send_header_request(
					peer,
					self.id,
					data.block,
				),
			RequestData::RemoteRead(ref data, _) =>
				out.send_read_request(
					peer,
					self.id,
					data.block,
					data.key.clone(),
				),
			RequestData::RemoteReadChild(ref data, _) =>
				out.send_read_child_request(
					peer,
					self.id,
					data.block,
					data.storage_key.clone(),
					data.key.clone(),
				),
			RequestData::RemoteCall(ref data, _) =>
				out.send_call_request(
					peer,
					self.id,
					data.block,
					data.method.clone(),
					data.call_data.clone(),
				),
			RequestData::RemoteChanges(ref data, _) =>
				out.send_changes_request(
					peer,
					self.id,
					data.first_block.1.clone(),
					data.last_block.1.clone(),
					data.tries_roots.1.clone(),
					data.max_block.1.clone(),
					data.key.clone(),
				),
			RequestData::RemoteBody(ref data, _) =>
				out.send_body_request(
					peer,
					self.id,
					message::BlockAttributes::BODY,
					message::FromBlock::Hash(data.header.hash()),
					None,
					message::Direction::Ascending,
					Some(1)
				),
		}
	}
}

impl<Block: BlockT> RequestData<Block> {
	fn fail(self, error: ClientError) {
		// don't care if anyone is listening
		match self {
			RequestData::RemoteHeader(_, sender) => { let _ = sender.send(Err(error)); },
			RequestData::RemoteCall(_, sender) => { let _ = sender.send(Err(error)); },
			RequestData::RemoteRead(_, sender) => { let _ = sender.send(Err(error)); },
			RequestData::RemoteReadChild(_, sender) => { let _ = sender.send(Err(error)); },
			RequestData::RemoteChanges(_, sender) => { let _ = sender.send(Err(error)); },
			RequestData::RemoteBody(_, sender) => { let _ = sender.send(Err(error)); },
		}
	}
}

#[cfg(test)]
pub mod tests {
	use std::collections::HashSet;
	use std::sync::Arc;
	use std::time::Instant;
	use futures::{Future, sync::oneshot};
	use runtime_primitives::traits::{Block as BlockT, NumberFor, Header as HeaderT};
	use client::{error::{Error as ClientError, Result as ClientResult}};
	use client::light::fetcher::{FetchChecker, RemoteHeaderRequest,
		ChangesProof,	RemoteCallRequest, RemoteReadRequest,
		RemoteReadChildRequest, RemoteChangesRequest, RemoteBodyRequest};
	use crate::config::Roles;
	use crate::message::{self, BlockAttributes, Direction, FromBlock, RequestId};
	use network_libp2p::PeerId;
	use super::{REQUEST_TIMEOUT, OnDemandCore, OnDemandNetwork, RequestData};
	use test_client::runtime::{changes_trie_config, Block, Extrinsic, Header};

	struct DummyFetchChecker { ok: bool }

	impl FetchChecker<Block> for DummyFetchChecker {
		fn check_header_proof(
			&self,
			_request: &RemoteHeaderRequest<Header>,
			header: Option<Header>,
			_remote_proof: Vec<Vec<u8>>
		) -> ClientResult<Header> {
			match self.ok {
				true if header.is_some() => Ok(header.unwrap()),
				_ => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_proof(&self, _: &RemoteReadRequest<Header>, _: Vec<Vec<u8>>) -> ClientResult<Option<Vec<u8>>> {
			match self.ok {
				true => Ok(Some(vec![42])),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_read_child_proof(
			&self,
			_: &RemoteReadChildRequest<Header>,
			_: Vec<Vec<u8>>
		) -> ClientResult<Option<Vec<u8>>> {
			match self.ok {
				true => Ok(Some(vec![42])),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_execution_proof(&self, _: &RemoteCallRequest<Header>, _: Vec<Vec<u8>>) -> ClientResult<Vec<u8>> {
			match self.ok {
				true => Ok(vec![42]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_changes_proof(
			&self,
			_: &RemoteChangesRequest<Header>,
			_: ChangesProof<Header>
		) -> ClientResult<Vec<(NumberFor<Block>, u32)>> {
			match self.ok {
				true => Ok(vec![(100, 2)]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}

		fn check_body_proof(
			&self,
			_: &RemoteBodyRequest<Header>,
			body: Vec<Extrinsic>
		) -> ClientResult<Vec<Extrinsic>> {
			match self.ok {
				true => Ok(body),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}
	}

	fn dummy(ok: bool) -> OnDemandCore<Block> {
		OnDemandCore::new(Arc::new(DummyFetchChecker { ok }))
	}

	fn total_peers(on_demand: &OnDemandCore<Block>) -> usize {
		on_demand.idle_peers.len() + on_demand.active_peers.len()
	}

	fn receive_call_response(
		network_interface: impl OnDemandNetwork<Block>,
		on_demand: &mut OnDemandCore<Block>,
		peer: PeerId,
		id: message::RequestId
	) {
		on_demand.on_remote_call_response(network_interface, peer, message::RemoteCallResponse {
			id: id,
			proof: vec![vec![2]],
		});
	}

	fn dummy_header() -> Header {
		Header {
			parent_hash: Default::default(),
			number: 0,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		}
	}

	#[derive(Default)]
	struct DummyNetwork {
		disconnected_peers: HashSet<PeerId>,
	}

	impl<'a, B: BlockT> OnDemandNetwork<B> for &'a mut DummyNetwork {
		fn report_peer(&mut self, _: &PeerId, _: i32) {}
		fn disconnect_peer(&mut self, who: &PeerId) {
			self.disconnected_peers.insert(who.clone());
		}
		fn send_header_request(&mut self, _: &PeerId, _: RequestId, _: <<B as BlockT>::Header as HeaderT>::Number) {}
		fn send_read_request(&mut self, _: &PeerId, _: RequestId, _: <B as BlockT>::Hash, _: Vec<u8>) {}
		fn send_read_child_request(&mut self, _: &PeerId, _: RequestId, _: <B as BlockT>::Hash, _: Vec<u8>,
			_: Vec<u8>) {}
		fn send_call_request(&mut self, _: &PeerId, _: RequestId, _: <B as BlockT>::Hash, _: String, _: Vec<u8>) {}
		fn send_changes_request(&mut self, _: &PeerId, _: RequestId, _: <B as BlockT>::Hash, _: <B as BlockT>::Hash,
			_: <B as BlockT>::Hash, _: <B as BlockT>::Hash, _: Vec<u8>) {}
		fn send_body_request(&mut self, _: &PeerId, _: RequestId, _: BlockAttributes, _: FromBlock<<B as BlockT>::Hash,
			<<B as BlockT>::Header as HeaderT>::Number>, _: Option<B::Hash>, _: Direction, _: Option<u32>) {}
	}

	fn assert_disconnected_peer(dummy: &DummyNetwork) {
		assert_eq!(dummy.disconnected_peers.len(), 1);
	}

	#[test]
	fn knows_about_peers_roles() {
		let mut network_interface = DummyNetwork::default();
		let mut on_demand = dummy(true);
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0, Roles::LIGHT, 1000);
		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 2000);
		on_demand.on_connect(&mut network_interface, peer2.clone(), Roles::AUTHORITY, 3000);
		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.best_blocks.get(&peer1), Some(&2000));
		assert_eq!(on_demand.best_blocks.get(&peer2), Some(&3000));
	}

	#[test]
	fn disconnects_from_idle_peer() {
		let peer0 = PeerId::random();

		let mut network_interface = DummyNetwork::default();
		let mut on_demand = dummy(true);
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 100);
		assert_eq!(1, total_peers(&on_demand));
		assert!(!on_demand.best_blocks.is_empty());

		on_demand.on_disconnect(&mut network_interface, peer0);
		assert_eq!(0, total_peers(&on_demand));
		assert!(on_demand.best_blocks.is_empty());
	}

	#[test]
	fn disconnects_from_timeouted_peer() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);
		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 1000);
		assert_eq!(vec![peer0.clone(), peer1.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert!(on_demand.active_peers.is_empty());

		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		}, oneshot::channel().0));
		assert_eq!(vec![peer1.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(vec![peer0.clone()], on_demand.active_peers.keys().cloned().collect::<Vec<_>>());

		on_demand.active_peers[&peer0].timestamp = Instant::now() - REQUEST_TIMEOUT - REQUEST_TIMEOUT;
		on_demand.maintain_peers(&mut network_interface);
		assert!(on_demand.idle_peers.is_empty());
		assert_eq!(vec![peer1.clone()], on_demand.active_peers.keys().cloned().collect::<Vec<_>>());
		assert_disconnected_peer(&network_interface);
	}

	#[test]
	fn disconnects_from_peer_on_response_with_wrong_id() {
		let mut on_demand = dummy(true);
		let peer0 = PeerId::random();
		let mut network_interface = DummyNetwork::default();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		}, oneshot::channel().0));
		receive_call_response(&mut network_interface, &mut on_demand, peer0, 1);
		assert_disconnected_peer(&network_interface);
		assert_eq!(on_demand.pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_incorrect_response() {
		let mut on_demand = dummy(false);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		}, oneshot::channel().0));

		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);
		receive_call_response(&mut network_interface, &mut on_demand, peer0.clone(), 0);
		assert_disconnected_peer(&network_interface);
		assert_eq!(on_demand.pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_unexpected_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		receive_call_response(&mut network_interface, &mut on_demand, peer0, 0);
		assert_disconnected_peer(&network_interface);
	}

	#[test]
	fn disconnects_from_peer_on_wrong_response_type() {
		let mut on_demand = dummy(false);
		let peer0 = PeerId::random();
		let mut network_interface = DummyNetwork::default();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		}, oneshot::channel().0));

		on_demand.on_remote_read_response(&mut network_interface, peer0.clone(), message::RemoteReadResponse {
			id: 0,
			proof: vec![vec![2]],
		});
		assert_disconnected_peer(&network_interface);
		assert_eq!(on_demand.pending_requests.len(), 1);
	}

	#[test]
	fn receives_remote_failure_after_retry_count_failures() {
		use parking_lot::{Condvar, Mutex};

		let retry_count = 2;
		let peer_ids = (0 .. retry_count + 1).map(|_| PeerId::random()).collect::<Vec<_>>();
		let mut on_demand = dummy(false);
		let mut network_interface = DummyNetwork::default();
		for i in 0..retry_count+1 {
			on_demand.on_connect(&mut network_interface, peer_ids[i].clone(), Roles::FULL, 1000);
		}

		let sync = Arc::new((Mutex::new(0), Mutex::new(0), Condvar::new()));
		let thread_sync = sync.clone();

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(retry_count)
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let &(ref current, ref finished_at, ref finished) = &*thread_sync;
			let _ = response.wait().unwrap().unwrap_err();
			*finished_at.lock() = *current.lock();
			finished.notify_one();
		});

		let &(ref current, ref finished_at, ref finished) = &*sync;
		for i in 0..retry_count+1 {
			let mut current = current.lock();
			*current = *current + 1;
			receive_call_response(&mut network_interface, &mut on_demand, peer_ids[i].clone(), i as u64);
		}

		let mut finished_at = finished_at.lock();
		assert!(!finished.wait_for(&mut finished_at, ::std::time::Duration::from_millis(1000)).timed_out());
		assert_eq!(*finished_at, retry_count + 1);

		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_call_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteCall(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap().unwrap();
			assert_eq!(result, vec![42]);
		});

		receive_call_response(&mut network_interface, &mut on_demand, peer0.clone(), 0);
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_read_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteRead(RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			key: b":key".to_vec(),
			retry_count: None,
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap().unwrap();
			assert_eq!(result, Some(vec![42]));
		});

		on_demand.on_remote_read_response(&mut network_interface, peer0.clone(), message::RemoteReadResponse {
			id: 0,
			proof: vec![vec![2]],
		});
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_read_child_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteReadChild(RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: b":child_storage:sub".to_vec(),
			key: b":key".to_vec(),
			retry_count: None,
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap().unwrap();
			assert_eq!(result, Some(vec![42]));
		});

		on_demand.on_remote_read_response(&mut network_interface,
			peer0.clone(), message::RemoteReadResponse {
				id: 0,
				proof: vec![vec![2]],
		});
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_header_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap().unwrap();
			assert_eq!(
				result.hash(),
				"6443a0b46e0412e626363028115a9f2c\
				 f963eeed526b8b33e5316f08b50d0dc3".parse().unwrap()
			);
		});

		on_demand.on_remote_header_response(&mut network_interface, peer0.clone(), message::RemoteHeaderResponse {
			id: 0,
			header: Some(Header {
				parent_hash: Default::default(),
				number: 1,
				state_root: Default::default(),
				extrinsics_root: Default::default(),
				digest: Default::default(),
			}),
			proof: vec![vec![2]],
		});
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_changes_response() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer0 = PeerId::random();
		on_demand.on_connect(&mut network_interface, peer0.clone(), Roles::FULL, 1000);

		let (tx, response) = oneshot::channel();
		on_demand.add_request(&mut network_interface, RequestData::RemoteChanges(RemoteChangesRequest {
			changes_trie_config: changes_trie_config(),
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), vec![]),
			key: vec![],
			retry_count: None,
		}, tx));
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap().unwrap();
			assert_eq!(result, vec![(100, 2)]);
		});

		on_demand.on_remote_changes_response(&mut network_interface, peer0.clone(), message::RemoteChangesResponse {
			id: 0,
			max: 1000,
			proof: vec![vec![2]],
			roots: vec![],
			roots_proof: vec![],
		});
		thread.join().unwrap();
	}

	#[test]
	fn does_not_sends_request_to_peer_who_has_no_required_block() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();

		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 100);

		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 200,
			retry_count: None,
		}, oneshot::channel().0));
		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		}, oneshot::channel().0));
		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		}, oneshot::channel().0));

		on_demand.on_connect(&mut network_interface, peer2.clone(), Roles::FULL, 150);

		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.pending_requests.len(), 3);

		on_demand.on_block_announce(&mut network_interface, peer1.clone(), 250);

		assert_eq!(vec![peer2.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.pending_requests.len(), 2);

		on_demand.on_block_announce(&mut network_interface, peer2.clone(), 250);

		assert!(!on_demand.idle_peers.iter().any(|_| true));
		assert_eq!(on_demand.pending_requests.len(), 1);

		on_demand.on_remote_header_response(&mut network_interface, peer1.clone(), message::RemoteHeaderResponse {
			id: 0,
			header: Some(dummy_header()),
			proof: vec![],
		});

		assert!(!on_demand.idle_peers.iter().any(|_| true));
		assert_eq!(on_demand.pending_requests.len(), 0);
	}

	#[test]
	fn does_not_loop_forever_after_dispatching_request_to_last_peer() {
		// this test is a regression for a bug where the dispatch function would
		// loop forever after dispatching a request to the last peer, since the
		// last peer was not updated
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let peer3 = PeerId::random();

		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		}, oneshot::channel().0));
		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		}, oneshot::channel().0));

		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 200);
		on_demand.on_connect(&mut network_interface, peer2.clone(), Roles::FULL, 200);
		on_demand.on_connect(&mut network_interface, peer3.clone(), Roles::FULL, 250);

		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.pending_requests.len(), 1);
	}

	#[test]
	fn tries_to_send_all_pending_requests() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer1 = PeerId::random();

		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 300,
			retry_count: None,
		}, oneshot::channel().0));
		on_demand.add_request(&mut network_interface, RequestData::RemoteHeader(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		}, oneshot::channel().0));

		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 250);

		assert!(on_demand.idle_peers.iter().cloned().collect::<Vec<_>>().is_empty());
		assert_eq!(on_demand.pending_requests.len(), 1);
	}

	#[test]
	fn remote_body_with_one_block_body_should_succeed() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer1 = PeerId::random();

		let header = dummy_header();
		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 250);

		on_demand.add_request(&mut network_interface, RequestData::RemoteBody(RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		}, oneshot::channel().0));

		assert!(on_demand.pending_requests.is_empty());
		assert_eq!(on_demand.active_peers.len(), 1);

		let block = message::BlockData::<Block> {
			hash: primitives::H256::random(),
			header: None,
			body: Some(Vec::new()),
			message_queue: None,
			receipt: None,
			justification: None,
		};

		let response = message::generic::BlockResponse {
			id: 0,
			blocks: vec![block],
		};

		on_demand.on_remote_body_response(&mut network_interface, peer1.clone(), response);

		assert!(on_demand.active_peers.is_empty());
		assert_eq!(on_demand.idle_peers.len(), 1);
	}

	#[test]
	fn remote_body_with_three_bodies_should_fail() {
		let mut on_demand = dummy(true);
		let mut network_interface = DummyNetwork::default();
		let peer1 = PeerId::random();

		let header = dummy_header();
		on_demand.on_connect(&mut network_interface, peer1.clone(), Roles::FULL, 250);

		on_demand.add_request(&mut network_interface, RequestData::RemoteBody(RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		}, oneshot::channel().0));

		assert!(on_demand.pending_requests.is_empty());
		assert_eq!(on_demand.active_peers.len(), 1);

		let response = {
			let blocks: Vec<_> = (0..3).map(|_| message::BlockData::<Block> {
				hash: primitives::H256::random(),
				header: None,
				body: Some(Vec::new()),
				message_queue: None,
				receipt: None,
				justification: None,
			}).collect();

			message::generic::BlockResponse {
				id: 0,
				blocks,
			}
		};

		on_demand.on_remote_body_response(&mut network_interface, peer1.clone(), response);
		assert!(on_demand.active_peers.is_empty());
		assert!(on_demand.idle_peers.is_empty(), "peer should be disconnected after bad response");
	}
}
