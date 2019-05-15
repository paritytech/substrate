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
use std::sync::{Arc, Weak};
use std::time::{Instant, Duration};
use log::{trace, info};
use futures::{Async, Future, Poll};
use futures::sync::oneshot::{channel, Receiver, Sender as OneShotSender};
use linked_hash_map::{Entry, LinkedHashMap};
use parity_codec::Encode;
use parking_lot::Mutex;
use client::error::Error as ClientError;
use client::light::fetcher::{Fetcher, FetchChecker, RemoteHeaderRequest,
	RemoteCallRequest, RemoteReadRequest, RemoteChangesRequest, ChangesProof,
	RemoteReadChildRequest, RemoteBodyRequest};
use crate::message;
use network_libp2p::PeerId;
use crate::config::Roles;
use crate::service::Service as NetworkService;
use crate::specialization::NetworkSpecialization;
use runtime_primitives::traits::{Block as BlockT, Hash, Header as HeaderT, NumberFor, HashFor};

/// Remote request timeout.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(15);
/// Default request retry count.
const RETRY_COUNT: usize = 1;
/// Reputation change for a peer when a request timed out.
const TIMEOUT_REPUTATION_CHANGE: i32 = -(1 << 8);

/// On-demand service API.
pub trait OnDemandService<Block: BlockT>: Send + Sync {
	/// When new node is connected.
	fn on_connect(&self, peer: PeerId, role: Roles, best_number: NumberFor<Block>);

	/// When block is announced by the peer.
	fn on_block_announce(&self, peer: PeerId, best_number: NumberFor<Block>);

	/// When node is disconnected.
	fn on_disconnect(&self, peer: PeerId);

	/// Maintain peers requests.
	fn maintain_peers(&self);

	/// When header response is received from remote node.
	fn on_remote_header_response(
		&self,
		peer: PeerId,
		response: message::RemoteHeaderResponse<Block::Header>
	);

	/// When read response is received from remote node.
	fn on_remote_read_response(&self, peer: PeerId, response: message::RemoteReadResponse);

	/// When call response is received from remote node.
	fn on_remote_call_response(&self, peer: PeerId, response: message::RemoteCallResponse);

	/// When changes response is received from remote node.
	fn on_remote_changes_response(
		&self,
		peer: PeerId,
		response: message::RemoteChangesResponse<NumberFor<Block>, Block::Hash>
	);

	/// When body response is received from remote node.
	fn on_remote_body_response(
		&self,
		peer: PeerId,
		response: message::BlockResponse<Block>
	);

	/// Check whether a block response is an `on_demand` response
	fn is_on_demand_response(&self, peer: &PeerId, request_id: message::RequestId) -> bool;
}

/// Trait used by the `OnDemand` service to communicate messages back to the network.
pub trait OnDemandNetwork<B: BlockT> {
	/// Adjusts the reputation of the given peer.
	fn report_peer(&self, who: &PeerId, reputation_change: i32);

	/// Disconnect from the given peer. Used in case of misbehaviour.
	fn disconnect_peer(&self, who: &PeerId);

	/// Send a request to a peer.
	fn send_request(&self, who: &PeerId, message: message::Message<B>);
}

impl<B: BlockT, S: NetworkSpecialization<B>> OnDemandNetwork<B> for Weak<NetworkService<B, S>> {
	fn report_peer(&self, who: &PeerId, reputation_change: i32) {
		if let Some(service) = self.upgrade() {
			service.report_peer(who.clone(), reputation_change)
		}
	}

	fn disconnect_peer(&self, who: &PeerId) {
		if let Some(service) = self.upgrade() {
			service.disconnect_peer(who.clone())
		}
	}

	fn send_request(&self, who: &PeerId, message: message::Message<B>) {
		if let Some(service) = self.upgrade() {
			service.send_request(who.clone(), message)
		}
	}
}

/// On-demand requests service. Dispatches requests to appropriate peers.
pub struct OnDemand<B: BlockT> {
	core: Mutex<OnDemandCore<B>>,
	checker: Arc<FetchChecker<B>>,
	network_interface: Mutex<Option<Box<dyn OnDemandNetwork<B> + Send + Sync + 'static>>>,
}

/// On-demand remote call response.
pub struct RemoteResponse<T> {
	receiver: Receiver<Result<T, ClientError>>,
}

#[derive(Default)]
struct OnDemandCore<B: BlockT> {
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

enum RequestData<Block: BlockT> {
	RemoteBody(RemoteBodyRequest<Block::Header>, OneShotSender<Result<Vec<Block::Extrinsic>, ClientError>>),
	RemoteHeader(RemoteHeaderRequest<Block::Header>, OneShotSender<Result<Block::Header, ClientError>>),
	RemoteRead(RemoteReadRequest<Block::Header>, OneShotSender<Result<Option<Vec<u8>>, ClientError>>),
	RemoteReadChild(
		RemoteReadChildRequest<Block::Header>,
		OneShotSender<Result<Option<Vec<u8>>, ClientError>>
	),
	RemoteCall(RemoteCallRequest<Block::Header>, OneShotSender<Result<Vec<u8>, ClientError>>),
	RemoteChanges(RemoteChangesRequest<Block::Header>, OneShotSender<Result<Vec<(NumberFor<Block>, u32)>, ClientError>>),
}

enum Accept<Block: BlockT> {
	Ok,
	CheckFailed(ClientError, RequestData<Block>),
	Unexpected(RequestData<Block>),
}

impl<T> Future for RemoteResponse<T> {
	type Item = T;
	type Error = ClientError;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.receiver.poll()
			.map_err(|_| ClientError::RemoteFetchCancelled.into())
			.and_then(|r| match r {
				Async::Ready(Ok(ready)) => Ok(Async::Ready(ready)),
				Async::Ready(Err(error)) => Err(error),
				Async::NotReady => Ok(Async::NotReady),
			})
	}
}

impl<B: BlockT> OnDemand<B> where
	B::Header: HeaderT,
{
	/// Creates new on-demand service.
	pub fn new(checker: Arc<FetchChecker<B>>) -> Self {
		OnDemand {
			checker,
			network_interface: Mutex::new(None),
			core: Mutex::new(OnDemandCore {
				next_request_id: 0,
				pending_requests: VecDeque::new(),
				active_peers: LinkedHashMap::new(),
				idle_peers: VecDeque::new(),
				best_blocks: HashMap::new(),
			})
		}
	}

	/// Get checker reference.
	pub fn checker(&self) -> &Arc<FetchChecker<B>> {
		&self.checker
	}

	/// Sets weak reference to network service.
	pub fn set_network_interface(&self, network_interface: Box<dyn OnDemandNetwork<B> + Send + Sync + 'static>) {
		self.network_interface.lock().replace(network_interface);
	}

	fn report_peer(&self, who: &PeerId, reputation_change: i32) {
		self.network_interface
			.lock()
			.as_ref()
			.expect("1. OnDemand is passed a network sender upon initialization of the service, 2. it should bet set by now")
			.report_peer(who, reputation_change);
	}

	fn disconnect_peer(&self, who: &PeerId) {
		self.network_interface
			.lock()
			.as_ref()
			.expect("1. OnDemand is passed a network sender upon initialization of the service, 2. it should bet set by now")
			.disconnect_peer(who);
	}

	fn send_request(&self, who: &PeerId, msg: message::Message<B>) {
		self.network_interface
			.lock()
			.as_ref()
			.expect("1. OnDemand is passed a network sender upon initialization of the service, 2. it should bet set by now")
			.send_request(who, msg);
	}

	/// Schedule && dispatch all scheduled requests.
	fn schedule_request<R>(&self, retry_count: Option<usize>, data: RequestData<B>, result: R) -> R {
		let mut core = self.core.lock();
		core.insert(retry_count.unwrap_or(RETRY_COUNT), data);
		core.dispatch(self);
		result
	}

	/// Try to accept response from given peer.
	fn accept_response<F: FnOnce(Request<B>) -> Accept<B>>(&self, rtype: &str, peer: PeerId, request_id: u64, try_accept: F) {
		let mut core = self.core.lock();
		let request = match core.remove(peer.clone(), request_id) {
			Some(request) => request,
			None => {
				info!("Invalid remote {} response from peer {}", rtype, peer);
				self.report_peer(&peer, i32::min_value());
				self.disconnect_peer(&peer);
				core.remove_peer(peer);
				return;
			},
		};

		let retry_count = request.retry_count;
		let (retry_count, retry_request_data) = match try_accept(request) {
			Accept::Ok => (retry_count, None),
			Accept::CheckFailed(error, retry_request_data) => {
				info!("Failed to check remote {} response from peer {}: {}", rtype, peer, error);
				self.report_peer(&peer, i32::min_value());
				self.disconnect_peer(&peer);
				core.remove_peer(peer);

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
				self.report_peer(&peer, i32::min_value());
				self.disconnect_peer(&peer);
				core.remove_peer(peer);

				(retry_count, Some(retry_request_data))
			},
		};

		if let Some(request_data) = retry_request_data {
			core.insert(retry_count, request_data);
		}

		core.dispatch(self);
	}
}

impl<B> OnDemandService<B> for OnDemand<B> where
	B: BlockT,
	B::Header: HeaderT,
{
	fn on_connect(&self, peer: PeerId, role: Roles, best_number: NumberFor<B>) {
		if !role.is_full() {
			return;
		}

		let mut core = self.core.lock();
		core.add_peer(peer, best_number);
		core.dispatch(self);
	}

	fn on_block_announce(&self, peer: PeerId, best_number: NumberFor<B>) {
		let mut core = self.core.lock();
		core.update_peer(peer, best_number);
		core.dispatch(self);
	}

	fn on_disconnect(&self, peer: PeerId) {
		let mut core = self.core.lock();
		core.remove_peer(peer);
		core.dispatch(self);
	}

	fn maintain_peers(&self) {
		let mut core = self.core.lock();
		for bad_peer in core.maintain_peers() {
			self.report_peer(&bad_peer, TIMEOUT_REPUTATION_CHANGE);
			self.disconnect_peer(&bad_peer);
		}
		core.dispatch(self);
	}

	fn on_remote_header_response(&self, peer: PeerId, response: message::RemoteHeaderResponse<B::Header>) {
		self.accept_response("header", peer, response.id, |request| match request.data {
			RequestData::RemoteHeader(request, sender) => match self.checker.check_header_proof(&request, response.header, response.proof) {
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

	fn on_remote_read_response(&self, peer: PeerId, response: message::RemoteReadResponse) {
		self.accept_response("read", peer, response.id, |request| match request.data {
			RequestData::RemoteRead(request, sender) => {
				match self.checker.check_read_proof(&request, response.proof) {
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
				match self.checker.check_read_child_proof(&request, response.proof) {
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

	fn on_remote_call_response(&self, peer: PeerId, response: message::RemoteCallResponse) {
		self.accept_response("call", peer, response.id, |request| match request.data {
			RequestData::RemoteCall(request, sender) => match self.checker.check_execution_proof(&request, response.proof) {
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

	fn on_remote_changes_response(&self, peer: PeerId, response: message::RemoteChangesResponse<NumberFor<B>, B::Hash>) {
		self.accept_response("changes", peer, response.id, |request| match request.data {
			RequestData::RemoteChanges(request, sender) => match self.checker.check_changes_proof(
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

	fn on_remote_body_response(&self, peer: PeerId, response: message::BlockResponse<B>) {
		self.accept_response("body", peer, response.id, |request| match request.data {
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

				// TODO(niklasad1/svyatonik): there is nothing in the runtime that ensures that
				// `Header::extrinsics_root()` actually returns
				// `<Block>::ordered_trie_root(body.iter().map(Encode::encode))`.
				//
				// Thus, this may fail
				let	extrinsics_root = HashFor::<B>::ordered_trie_root(bodies.iter().map(Encode::encode));
				if *request.header.extrinsics_root() == extrinsics_root {
					let body = std::mem::replace(&mut bodies[0], Vec::new());
					let _ = sender.send(Ok(body));
					Accept::Ok
				} else {
					Accept::CheckFailed(
						format!("RemoteBodyRequest: invalid extrinsics root expected: {} but got {}",
								*request.header.extrinsics_root(),
								extrinsics_root,
						).into(),
						RequestData::RemoteBody(request, sender)
					)
				}
			}
			other => Accept::Unexpected(other),
		})
	}

	fn is_on_demand_response(&self, peer: &PeerId, request_id: message::RequestId) -> bool {
		// TODO(niklasad1): could make sense to use `RwLock` instead of `Mutex`
		let core = self.core.lock();
		core.is_pending_request(&peer, request_id)
	}
}

impl<B> Fetcher<B> for OnDemand<B> where
	B: BlockT,
	B::Header: HeaderT,
{
	type RemoteHeaderResult = RemoteResponse<B::Header>;
	type RemoteReadResult = RemoteResponse<Option<Vec<u8>>>;
	type RemoteCallResult = RemoteResponse<Vec<u8>>;
	type RemoteChangesResult = RemoteResponse<Vec<(NumberFor<B>, u32)>>;
	type RemoteBodyResult = RemoteResponse<Vec<B::Extrinsic>>;

	fn remote_header(&self, request: RemoteHeaderRequest<B::Header>) -> Self::RemoteHeaderResult {
		let (sender, receiver) = channel();
		self.schedule_request(request.retry_count.clone(), RequestData::RemoteHeader(request, sender),
			RemoteResponse { receiver })
	}

	fn remote_read(&self, request: RemoteReadRequest<B::Header>) -> Self::RemoteReadResult {
		let (sender, receiver) = channel();
		self.schedule_request(
			request.retry_count.clone(),
			RequestData::RemoteRead(request, sender),
			RemoteResponse { receiver }
		)
	}

	fn remote_read_child(
		&self,
		request: RemoteReadChildRequest<B::Header>
	) -> Self::RemoteReadResult {
		let (sender, receiver) = channel();
		self.schedule_request(
			request.retry_count.clone(),
			RequestData::RemoteReadChild(request, sender),
			RemoteResponse { receiver }
		)
	}

	fn remote_call(&self, request: RemoteCallRequest<B::Header>) -> Self::RemoteCallResult {
		let (sender, receiver) = channel();
		self.schedule_request(request.retry_count.clone(), RequestData::RemoteCall(request, sender),
			RemoteResponse { receiver })
	}

	fn remote_changes(&self, request: RemoteChangesRequest<B::Header>) -> Self::RemoteChangesResult {
		let (sender, receiver) = channel();
		self.schedule_request(request.retry_count.clone(), RequestData::RemoteChanges(request, sender),
			RemoteResponse { receiver })
	}

	fn remote_body(&self, request: RemoteBodyRequest<B::Header>) -> Self::RemoteBodyResult {
		let (sender, receiver) = channel();
		self.schedule_request(request.retry_count.clone(), RequestData::RemoteBody(request, sender),
			RemoteResponse { receiver })
	}
}

impl<B> OnDemandCore<B> where
	B: BlockT,
	B::Header: HeaderT,
{
	fn is_pending_request(&self, peer: &PeerId, request_id: message::RequestId) -> bool {
		self.active_peers.get(&peer).map_or(false, |r| r.id == request_id)
	}

	pub fn add_peer(&mut self, peer: PeerId, best_number: NumberFor<B>) {
		self.idle_peers.push_back(peer.clone());
		self.best_blocks.insert(peer, best_number);
	}

	pub fn update_peer(&mut self, peer: PeerId, best_number: NumberFor<B>) {
		self.best_blocks.insert(peer, best_number);
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

	pub fn maintain_peers(&mut self) -> Vec<PeerId> {
		let now = Instant::now();
		let mut bad_peers = Vec::new();
		loop {
			match self.active_peers.front() {
				Some((_, request)) if now - request.timestamp >= REQUEST_TIMEOUT => (),
				_ => return bad_peers,
			}

			let (bad_peer, request) = self.active_peers.pop_front().expect("front() is Some as checked above");
			self.pending_requests.push_front(request);
			bad_peers.push(bad_peer);
		}
	}

	pub fn insert(&mut self, retry_count: usize, data: RequestData<B>) {
		let request_id = self.next_request_id;
		self.next_request_id += 1;

		self.pending_requests.push_back(Request {
			id: request_id,
			timestamp: Instant::now(),
			retry_count,
			data,
		});
	}

	pub fn remove(&mut self, peer: PeerId, id: u64) -> Option<Request<B>> {
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

	pub fn dispatch(&mut self, on_demand: &OnDemand<B>) {

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
			on_demand.send_request(&peer, request.message());
			self.active_peers.insert(peer, request);
		}

		self.pending_requests.append(&mut unhandled_requests);
	}
}

impl<Block: BlockT> Request<Block> {
	pub fn required_block(&self) -> NumberFor<Block> {
		match self.data {
			RequestData::RemoteHeader(ref data, _) => data.block,
			RequestData::RemoteRead(ref data, _) => *data.header.number(),
			RequestData::RemoteReadChild(ref data, _) => *data.header.number(),
			RequestData::RemoteCall(ref data, _) => *data.header.number(),
			RequestData::RemoteChanges(ref data, _) => data.max_block.0,
			RequestData::RemoteBody(ref data, _) => *data.header.number(),
		}
	}

	pub fn message(&self) -> message::Message<Block> {
		match self.data {
			RequestData::RemoteHeader(ref data, _) =>
				message::generic::Message::RemoteHeaderRequest(message::RemoteHeaderRequest {
					id: self.id,
					block: data.block,
				}),
			RequestData::RemoteRead(ref data, _) =>
				message::generic::Message::RemoteReadRequest(message::RemoteReadRequest {
					id: self.id,
					block: data.block,
					key: data.key.clone(),
				}),
			RequestData::RemoteReadChild(ref data, _) =>
				message::generic::Message::RemoteReadChildRequest(
					message::RemoteReadChildRequest {
						id: self.id,
						block: data.block,
						storage_key: data.storage_key.clone(),
						key: data.key.clone(),
				}),
			RequestData::RemoteCall(ref data, _) =>
				message::generic::Message::RemoteCallRequest(message::RemoteCallRequest {
					id: self.id,
					block: data.block,
					method: data.method.clone(),
					data: data.call_data.clone(),
				}),
			RequestData::RemoteChanges(ref data, _) =>
				message::generic::Message::RemoteChangesRequest(message::RemoteChangesRequest {
					id: self.id,
					first: data.first_block.1.clone(),
					last: data.last_block.1.clone(),
					min: data.tries_roots.1.clone(),
					max: data.max_block.1.clone(),
					key: data.key.clone(),
				}),
			RequestData::RemoteBody(ref data, _) => {
				message::generic::Message::BlockRequest(message::BlockRequest::<Block> {
					id: self.id,
					fields: message::BlockAttributes::BODY,
					from: message::FromBlock::Hash(data.header.hash()),
					to: None,
					direction: message::Direction::Ascending,
					max: Some(1),
				})
			}
		}
	}
}

impl<Block: BlockT> RequestData<Block> {
	pub fn fail(self, error: ClientError) {
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
	use std::sync::{Arc, Mutex};
	use std::time::Instant;
	use futures::Future;
	use runtime_primitives::traits::{Block as BlockT, NumberFor};
	use client::{error::{Error as ClientError, Result as ClientResult}};
	use client::light::fetcher::{Fetcher, FetchChecker, RemoteHeaderRequest,
		ChangesProof,	RemoteCallRequest, RemoteReadRequest,
		RemoteReadChildRequest, RemoteChangesRequest};
	use crate::config::Roles;
	use crate::message;
	use network_libp2p::PeerId;
	use super::{REQUEST_TIMEOUT, OnDemand, OnDemandNetwork, OnDemandService};
	use test_client::runtime::{changes_trie_config, Block, Header};

	pub struct DummyExecutor;
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

		fn check_changes_proof(&self, _: &RemoteChangesRequest<Header>, _: ChangesProof<Header>) -> ClientResult<Vec<(NumberFor<Block>, u32)>> {
			match self.ok {
				true => Ok(vec![(100, 2)]),
				false => Err(ClientError::Backend("Test error".into())),
			}
		}
	}

	fn dummy(ok: bool) -> (Arc<DummyExecutor>, Arc<OnDemand<Block>>) {
		let executor = Arc::new(DummyExecutor);
		let service = Arc::new(OnDemand::new(Arc::new(DummyFetchChecker { ok })));
		(executor, service)
	}

	fn total_peers(on_demand: &OnDemand<Block>) -> usize {
		let core = on_demand.core.lock();
		core.idle_peers.len() + core.active_peers.len()
	}

	fn receive_call_response(on_demand: &OnDemand<Block>, peer: PeerId, id: message::RequestId) {
		on_demand.on_remote_call_response(peer, message::RemoteCallResponse {
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
		disconnected_peers: Mutex<HashSet<PeerId>>,
	}

	impl<B: BlockT> OnDemandNetwork<B> for Arc<DummyNetwork> {
		fn report_peer(&self, _: &PeerId, _: i32) {}
		fn disconnect_peer(&self, who: &PeerId) {
			self.disconnected_peers.lock().unwrap().insert(who.clone());
		}
		fn send_request(&self, _: &PeerId, _: message::Message<B>) {}
	}

	fn assert_disconnected_peer(dummy: Arc<DummyNetwork>) {
		assert_eq!(dummy.disconnected_peers.lock().unwrap().len(), 1);
	}

	#[test]
	fn knows_about_peers_roles() {
		let (_, on_demand) = dummy(true);
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		on_demand.on_connect(peer0, Roles::LIGHT, 1000);
		on_demand.on_connect(peer1.clone(), Roles::FULL, 2000);
		on_demand.on_connect(peer2.clone(), Roles::AUTHORITY, 3000);
		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.core.lock().best_blocks.get(&peer1), Some(&2000));
		assert_eq!(on_demand.core.lock().best_blocks.get(&peer2), Some(&3000));
	}

	#[test]
	fn disconnects_from_idle_peer() {
		let peer0 = PeerId::random();

		let (_, on_demand) = dummy(true);
		on_demand.on_connect(peer0.clone(), Roles::FULL, 100);
		assert_eq!(1, total_peers(&*on_demand));
		assert!(!on_demand.core.lock().best_blocks.is_empty());

		on_demand.on_disconnect(peer0);
		assert_eq!(0, total_peers(&*on_demand));
		assert!(on_demand.core.lock().best_blocks.is_empty());
	}

	#[test]
	fn disconnects_from_timeouted_peer() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		let peer1 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);
		on_demand.on_connect(peer1.clone(), Roles::FULL, 1000);
		assert_eq!(vec![peer0.clone(), peer1.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert!(on_demand.core.lock().active_peers.is_empty());

		on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		});
		assert_eq!(vec![peer1.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(vec![peer0.clone()], on_demand.core.lock().active_peers.keys().cloned().collect::<Vec<_>>());

		on_demand.core.lock().active_peers[&peer0].timestamp = Instant::now() - REQUEST_TIMEOUT - REQUEST_TIMEOUT;
		on_demand.maintain_peers();
		assert!(on_demand.core.lock().idle_peers.is_empty());
		assert_eq!(vec![peer1.clone()], on_demand.core.lock().active_peers.keys().cloned().collect::<Vec<_>>());
		assert_disconnected_peer(network_interface);
	}

	#[test]
	fn disconnects_from_peer_on_response_with_wrong_id() {
		let (_x, on_demand) = dummy(true);
		let peer0 = PeerId::random();
		let network_interface = Arc::new(DummyNetwork::default());
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		});
		receive_call_response(&*on_demand, peer0, 1);
		assert_disconnected_peer(network_interface);
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_incorrect_response() {
		let (_x, on_demand) = dummy(false);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		});

		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);
		receive_call_response(&*on_demand, peer0.clone(), 0);
		assert_disconnected_peer(network_interface);
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_unexpected_response() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		receive_call_response(&*on_demand, peer0, 0);
		assert_disconnected_peer(network_interface);
	}

	#[test]
	fn disconnects_from_peer_on_wrong_response_type() {
		let (_x, on_demand) = dummy(false);
		let peer0 = PeerId::random();
		let network_interface = Arc::new(DummyNetwork::default());
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(1),
		});

		on_demand.on_remote_read_response(peer0.clone(), message::RemoteReadResponse {
			id: 0,
			proof: vec![vec![2]],
		});
		assert_disconnected_peer(network_interface);
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn receives_remote_failure_after_retry_count_failures() {
		use parking_lot::{Condvar, Mutex};

		let retry_count = 2;
		let peer_ids = (0 .. retry_count + 1).map(|_| PeerId::random()).collect::<Vec<_>>();
		let (_x, on_demand) = dummy(false);
		let network_interface = Arc::new(DummyNetwork::default());
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		for i in 0..retry_count+1 {
			on_demand.on_connect(peer_ids[i].clone(), Roles::FULL, 1000);
		}

		let sync = Arc::new((Mutex::new(0), Mutex::new(0), Condvar::new()));
		let thread_sync = sync.clone();

		let response = on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: Some(retry_count)
		});
		let thread = ::std::thread::spawn(move || {
			let &(ref current, ref finished_at, ref finished) = &*thread_sync;
			let _ = response.wait().unwrap_err();
			*finished_at.lock() = *current.lock();
			finished.notify_one();
		});

		let &(ref current, ref finished_at, ref finished) = &*sync;
		for i in 0..retry_count+1 {
			let mut current = current.lock();
			*current = *current + 1;
			receive_call_response(&*on_demand, peer_ids[i].clone(), i as u64);
		}

		let mut finished_at = finished_at.lock();
		assert!(!finished.wait_for(&mut finished_at, ::std::time::Duration::from_millis(1000)).timed_out());
		assert_eq!(*finished_at, retry_count + 1);

		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_call_response() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		let response = on_demand.remote_call(RemoteCallRequest {
			block: Default::default(),
			header: dummy_header(),
			method: "test".into(),
			call_data: vec![],
			retry_count: None,
		});
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(result, vec![42]);
		});

		receive_call_response(&*on_demand, peer0.clone(), 0);
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_read_response() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		let response = on_demand.remote_read(RemoteReadRequest {
			header: dummy_header(),
			block: Default::default(),
			key: b":key".to_vec(),
			retry_count: None,
		});
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(result, Some(vec![42]));
		});

		on_demand.on_remote_read_response(peer0.clone(), message::RemoteReadResponse {
			id: 0,
			proof: vec![vec![2]],
		});
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_read_child_response() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		let response = on_demand.remote_read_child(RemoteReadChildRequest {
			header: dummy_header(),
			block: Default::default(),
			storage_key: b":child_storage:sub".to_vec(),
			key: b":key".to_vec(),
			retry_count: None,
		});
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(result, Some(vec![42]));
		});

		on_demand.on_remote_read_response(
			peer0.clone(), message::RemoteReadResponse {
				id: 0,
				proof: vec![vec![2]],
		});
		thread.join().unwrap();
	}

	#[test]
	fn receives_remote_header_response() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		let response = on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		});
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(
				result.hash(),
				"6443a0b46e0412e626363028115a9f2c\
				 f963eeed526b8b33e5316f08b50d0dc3".parse().unwrap()
			);
		});

		on_demand.on_remote_header_response(peer0.clone(), message::RemoteHeaderResponse {
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
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer0 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));
		on_demand.on_connect(peer0.clone(), Roles::FULL, 1000);

		let response = on_demand.remote_changes(RemoteChangesRequest {
			changes_trie_config: changes_trie_config(),
			first_block: (1, Default::default()),
			last_block: (100, Default::default()),
			max_block: (100, Default::default()),
			tries_roots: (1, Default::default(), vec![]),
			key: vec![],
			retry_count: None,
		});
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(result, vec![(100, 2)]);
		});

		on_demand.on_remote_changes_response(peer0.clone(), message::RemoteChangesResponse {
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
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));

		on_demand.on_connect(peer1.clone(), Roles::FULL, 100);

		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 200,
			retry_count: None,
		});
		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		});
		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		});

		on_demand.on_connect(peer2.clone(), Roles::FULL, 150);

		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.core.lock().pending_requests.len(), 3);

		on_demand.on_block_announce(peer1.clone(), 250);

		assert_eq!(vec![peer2.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.core.lock().pending_requests.len(), 2);

		on_demand.on_block_announce(peer2.clone(), 250);

		assert!(!on_demand.core.lock().idle_peers.iter().any(|_| true));
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);

		on_demand.on_remote_header_response(peer1.clone(), message::RemoteHeaderResponse {
			id: 0,
			header: Some(dummy_header()),
			proof: vec![],
		});

		assert!(!on_demand.core.lock().idle_peers.iter().any(|_| true));
		assert_eq!(on_demand.core.lock().pending_requests.len(), 0);
	}

	#[test]
	fn does_not_loop_forever_after_dispatching_request_to_last_peer() {
		// this test is a regression for a bug where the dispatch function would
		// loop forever after dispatching a request to the last peer, since the
		// last peer was not updated
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer1 = PeerId::random();
		let peer2 = PeerId::random();
		let peer3 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));

		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		});
		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		});

		on_demand.on_connect(peer1.clone(), Roles::FULL, 200);
		on_demand.on_connect(peer2.clone(), Roles::FULL, 200);
		on_demand.on_connect(peer3.clone(), Roles::FULL, 250);

		assert_eq!(vec![peer1.clone(), peer2.clone()], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn tries_to_send_all_pending_requests() {
		let (_x, on_demand) = dummy(true);
		let network_interface = Arc::new(DummyNetwork::default());
		let peer1 = PeerId::random();
		on_demand.set_network_interface(Box::new(network_interface.clone()));

		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 300,
			retry_count: None,
		});
		on_demand.remote_header(RemoteHeaderRequest {
			cht_root: Default::default(),
			block: 250,
			retry_count: None,
		});

		on_demand.on_connect(peer1.clone(), Roles::FULL, 250);

		assert!(on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>().is_empty());
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}
}
