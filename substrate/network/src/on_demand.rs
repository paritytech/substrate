// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! On-demand requests service.

use std::collections::VecDeque;
use std::sync::{Arc, Weak};
use std::time::{Instant, Duration};
use futures::{Future, Poll};
use futures::sync::oneshot::{channel, Receiver, Sender};
use linked_hash_map::LinkedHashMap;
use linked_hash_map::Entry;
use parking_lot::Mutex;
use client;
use client::light::{Fetcher, FetchChecker, RemoteCallRequest};
use io::SyncIo;
use message;
use network::PeerId;
use service;

/// Remote request timeout.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(15);

/// On-demand service API.
pub trait OnDemandService: Send + Sync {
	/// When new node is connected.
	fn on_connect(&self, peer: PeerId, role: service::Role);

	/// When node is disconnected.
	fn on_disconnect(&self, peer: PeerId);

	/// Maintain peers requests.
	fn maintain_peers(&self, io: &mut SyncIo);

	/// When response is received from remote node.
	fn on_remote_response(&self, io: &mut SyncIo, peer: PeerId, response: message::RemoteCallResponse);
}

/// On-demand requests service. Dispatches requests to appropriate peers.
pub struct OnDemand<E: service::ExecuteInContext> {
	core: Mutex<OnDemandCore<E>>,
	checker: Arc<FetchChecker>,
}

/// On-demand response.
pub struct Response {
	receiver: Receiver<client::CallResult>,
}

#[derive(Default)]
struct OnDemandCore<E: service::ExecuteInContext> {
	service: Weak<E>,
	next_request_id: u64,
	pending_requests: VecDeque<Request>,
	active_peers: LinkedHashMap<PeerId, Request>,
	idle_peers: VecDeque<PeerId>,
}

struct Request {
	id: u64,
	timestamp: Instant,
	sender: Sender<client::CallResult>,
	request: RemoteCallRequest,
}

impl Future for Response {
	type Item = client::CallResult;
	type Error = client::error::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.receiver.poll()
			.map_err(|_| client::error::ErrorKind::RemoteFetchCancelled.into())
	}
}

impl<E> OnDemand<E> where E: service::ExecuteInContext {
	/// Creates new on-demand service.
	pub fn new(checker: Arc<FetchChecker>) -> Self {
		OnDemand {
			checker,
			core: Mutex::new(OnDemandCore {
				service: Weak::new(),
				next_request_id: 0,
				pending_requests: VecDeque::new(),
				active_peers: LinkedHashMap::new(),
				idle_peers: VecDeque::new(),
			})
		}
	}

	/// Sets weak reference to network service.
	pub fn set_service_link(&self, service: Weak<E>) {
		self.core.lock().service = service;
	}

	/// Execute method call on remote node, returning execution result and proof.
	pub fn remote_call(&self, request: RemoteCallRequest) -> Response {
		let (sender, receiver) = channel();
		let result = Response {
			receiver: receiver,
		};

		{
			let mut core = self.core.lock();
			core.insert(sender, request);
			core.dispatch();
		}

		result
	}
}

impl<E> OnDemandService for OnDemand<E> where E: service::ExecuteInContext {
	fn on_connect(&self, peer: PeerId, role: service::Role) {
		if !role.intersects(service::Role::FULL | service::Role::COLLATOR | service::Role::VALIDATOR) { // TODO: correct?
			return;
		}

		let mut core = self.core.lock();
		core.add_peer(peer);
		core.dispatch();
	}

	fn on_disconnect(&self, peer: PeerId) {
		let mut core = self.core.lock();
		core.remove_peer(peer);
		core.dispatch();
	}

	fn maintain_peers(&self, io: &mut SyncIo) {
		let mut core = self.core.lock();
		for bad_peer in core.maintain_peers() {
			trace!(target: "sync", "Remote request timeout for peer {}", bad_peer);
			io.disconnect_peer(bad_peer);
		}
		core.dispatch();
	}

	fn on_remote_response(&self, io: &mut SyncIo, peer: PeerId, response: message::RemoteCallResponse) {
		let mut core = self.core.lock();
		match core.remove(peer, response.id) {
			Some(request) => match self.checker.check_execution_proof(&request.request, (response.value, response.proof)) {
				Ok(response) => {
					// we do not bother if receiver has been dropped already
					let _ = request.sender.send(response);
				},
				Err(error) => {
					trace!(target: "sync", "Failed to check remote response from peer {}: {}", peer, error);
					io.disconnect_peer(peer);
					core.remove_peer(peer);
					core.insert(request.sender, request.request);
				},
			},
			None => {
				trace!(target: "sync", "Invalid remote response from peer {}", peer);
				io.disconnect_peer(peer);
				core.remove_peer(peer);
			},
		}

		core.dispatch();
	}
}

impl<E> Fetcher for OnDemand<E> where E: service::ExecuteInContext {
	type RemoteCallResult = Response;

	fn remote_call(&self, request: RemoteCallRequest) -> Self::RemoteCallResult {
		self.remote_call(request)
	}
}

impl<E> OnDemandCore<E> where E: service::ExecuteInContext {
	pub fn add_peer(&mut self, peer: PeerId) {
		self.idle_peers.push_back(peer);
	}

	pub fn remove_peer(&mut self, peer: PeerId) {
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

	pub fn insert(&mut self, sender: Sender<client::CallResult>, request: RemoteCallRequest) {
		let request_id = self.next_request_id;
		self.next_request_id += 1;

		self.pending_requests.push_back(Request {
			id: request_id,
			timestamp: Instant::now(),
			sender,
			request,
		});
	}

	pub fn remove(&mut self, peer: PeerId, id: u64) -> Option<Request> {
		match self.active_peers.entry(peer) {
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

	pub fn dispatch(&mut self) {
		let service = match self.service.upgrade() {
			Some(service) => service,
			None => return,
		};

		while !self.pending_requests.is_empty() {
			let peer = match self.idle_peers.pop_front() {
				Some(peer) => peer,
				None => return,
			};

			let mut request = self.pending_requests.pop_front().expect("checked in loop condition; qed");
			request.timestamp = Instant::now();
			trace!(target: "sync", "Dispatching remote request {} to peer {}", request.id, peer);

			service.execute_in_context(|ctx, protocol| {
				let message = message::RemoteCallRequest {
					id: request.id,
					block: request.request.block,
					method: request.request.method.clone(),
					data: request.request.call_data.clone(),
				};

				protocol.send_message(ctx, peer, message::Message::RemoteCallRequest(message))
			});
			self.active_peers.insert(peer, request);
		}
	}
}

#[cfg(test)]
mod tests {
	use std::collections::VecDeque;
	use std::sync::Arc;
	use std::time::Instant;
	use futures::Future;
	use parking_lot::RwLock;
	use client;
	use client::light::{FetchChecker, RemoteCallRequest};
	use io::NetSyncIo;
	use message;
	use network::PeerId;
	use protocol::Protocol;
	use service::{Role, ExecuteInContext};
	use test::TestIo;
	use super::{REQUEST_TIMEOUT, OnDemand, OnDemandService};

	struct DummyExecutor;
	struct DummyFetchChecker { ok: bool }

	impl ExecuteInContext for DummyExecutor {
		fn execute_in_context<F: Fn(&mut NetSyncIo, &Protocol)>(&self, _closure: F) {}
	}

	impl FetchChecker for DummyFetchChecker {
		fn check_execution_proof(&self, _request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> client::error::Result<client::CallResult> {
			match self.ok {
				true => Ok(client::CallResult {
					return_data: remote_proof.0,
					changes: Default::default(),
				}),
				false => Err(client::error::ErrorKind::Backend("Test error".into()).into()),
			}
		}
	}

	fn dummy(ok: bool) -> (Arc<DummyExecutor>, Arc<OnDemand<DummyExecutor>>) {
		let executor = Arc::new(DummyExecutor);
		let service = Arc::new(OnDemand::new(Arc::new(DummyFetchChecker { ok })));
		service.set_service_link(Arc::downgrade(&executor));
		(executor, service)
	}

	fn total_peers(on_demand: &OnDemand<DummyExecutor>) -> usize {
		let core = on_demand.core.lock();
		core.idle_peers.len() + core.active_peers.len()
	}

	fn receive_response(on_demand: &OnDemand<DummyExecutor>, network: &mut TestIo, peer: PeerId, id: message::RequestId) {
		on_demand.on_remote_response(network, peer, message::RemoteCallResponse {
			id: id,
			value: vec![1],
			proof: vec![vec![2]],
		});
	}

	#[test]
	fn knows_about_peers_roles() {
		let (_, on_demand) = dummy(true);
		on_demand.on_connect(0, Role::LIGHT);
		on_demand.on_connect(1, Role::FULL);
		on_demand.on_connect(2, Role::COLLATOR);
		on_demand.on_connect(3, Role::VALIDATOR);
		assert_eq!(vec![1, 2, 3], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
	}

	#[test]
	fn disconnects_from_idle_peer() {
		let (_, on_demand) = dummy(true);
		on_demand.on_connect(0, Role::FULL);
		assert_eq!(1, total_peers(&*on_demand));
		on_demand.on_disconnect(0);
		assert_eq!(0, total_peers(&*on_demand));
	}

	#[test]
	fn disconnects_from_timeouted_peer() {
		let (_x, on_demand) = dummy(true);
		let queue = RwLock::new(VecDeque::new());
		let mut network = TestIo::new(&queue, None);

		on_demand.on_connect(0, Role::FULL);
		on_demand.on_connect(1, Role::FULL);
		assert_eq!(vec![0, 1], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert!(on_demand.core.lock().active_peers.is_empty());

		on_demand.remote_call(RemoteCallRequest { block: Default::default(), method: "test".into(), call_data: vec![] });
		assert_eq!(vec![1], on_demand.core.lock().idle_peers.iter().cloned().collect::<Vec<_>>());
		assert_eq!(vec![0], on_demand.core.lock().active_peers.keys().cloned().collect::<Vec<_>>());

		on_demand.core.lock().active_peers[&0].timestamp = Instant::now() - REQUEST_TIMEOUT - REQUEST_TIMEOUT;
		on_demand.maintain_peers(&mut network);
		assert!(on_demand.core.lock().idle_peers.is_empty());
		assert_eq!(vec![1], on_demand.core.lock().active_peers.keys().cloned().collect::<Vec<_>>());
		assert!(network.to_disconnect.contains(&0));
	}

	#[test]
	fn disconnects_from_peer_on_response_with_wrong_id() {
		let (_x, on_demand) = dummy(true);
		let queue = RwLock::new(VecDeque::new());
		let mut network = TestIo::new(&queue, None);
		on_demand.on_connect(0, Role::FULL);

		on_demand.remote_call(RemoteCallRequest { block: Default::default(), method: "test".into(), call_data: vec![] });
		receive_response(&*on_demand, &mut network, 0, 1);
		assert!(network.to_disconnect.contains(&0));
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_incorrect_response() {
		let (_x, on_demand) = dummy(false);
		let queue = RwLock::new(VecDeque::new());
		let mut network = TestIo::new(&queue, None);
		on_demand.on_connect(0, Role::FULL);

		on_demand.remote_call(RemoteCallRequest { block: Default::default(), method: "test".into(), call_data: vec![] });
		receive_response(&*on_demand, &mut network, 0, 0);
		assert!(network.to_disconnect.contains(&0));
		assert_eq!(on_demand.core.lock().pending_requests.len(), 1);
	}

	#[test]
	fn disconnects_from_peer_on_unexpected_response() {
		let (_x, on_demand) = dummy(true);
		let queue = RwLock::new(VecDeque::new());
		let mut network = TestIo::new(&queue, None);
		on_demand.on_connect(0, Role::FULL);

		receive_response(&*on_demand, &mut network, 0, 0);
		assert!(network.to_disconnect.contains(&0));
	}

	#[test]
	fn receives_remote_response() {
		let (_x, on_demand) = dummy(true);
		let queue = RwLock::new(VecDeque::new());
		let mut network = TestIo::new(&queue, None);
		on_demand.on_connect(0, Role::FULL);

		let response = on_demand.remote_call(RemoteCallRequest { block: Default::default(), method: "test".into(), call_data: vec![] });
		let thread = ::std::thread::spawn(move || {
			let result = response.wait().unwrap();
			assert_eq!(result.return_data, vec![1]);
		});

		receive_response(&*on_demand, &mut network, 0, 0);
		thread.join().unwrap();
	}
}
