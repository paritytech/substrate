// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Fuzz test emulates network events and peer connection handling by `ProtocolController`
//! and `PeerStore` to discover possible inconsistencies in peer management.

use crate::{
	peer_store::{PeerStore, PeerStoreHandle, PeerStoreProvider},
	protocol_controller::{
		Direction, IncomingIndex, Message, ProtoSetConfig, ProtocolController, ProtocolHandle,
		SetId,
	},
	ReputationChange,
};
use futures::prelude::*;
use libp2p::PeerId;
use rand::{
	distributions::{Distribution, Uniform, WeightedIndex},
	seq::IteratorRandom,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver};
use std::{
	collections::{HashMap, HashSet},
	time::Duration,
};
use tokio::sync::oneshot;

/// Peer events as observed by `Notifications` / fuzz test.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
enum Event {
	/// Either API requested to disconnect from the peer, or the peer dropped.
	Disconnected,
	/// Incoming request.
	Incoming,
	/// Answer from PSM: accept.
	PsmAccept,
	/// Answer from PSM: reject.
	PsmReject,
	/// Command from PSM: connect.
	PsmConnect,
	/// Command from PSM: drop connection.
	PsmDrop,
}

/// Simplified peer state as thought by `Notifications` / fuzz test.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
enum State {
	/// Peer is not connected.
	Disconnected,
	/// We have an inbound connection, but have not decided yet whether to accept it.
	Incoming(IncomingIndex),
	/// Peer is connected via an inbound connection.
	Inbound,
	/// Peer is connected via an outbound connection.
	Outbound,
}

impl State {
	fn is_event_allowed(&self, event: Event) -> bool {
		match self {
			State::Disconnected => match event {
				// Note: `Event::PsmDrop` must be ignored in this state.
				Event::Incoming | Event::PsmConnect | Event::PsmDrop => true,
				_ => false,
			},
			State::Incoming(_) => match event {
				// Note: `Event::PsmDrop` and `Event::PsmConnect` must be ignored.
				// (They are ignored in `ConnectionFuzzer::handle_message`, so not listed here.)
				Event::PsmAccept | Event::PsmReject => true,
				_ => false,
			},
			State::Inbound => match event {
				// Note: `Event::PsmConnect` must be ignored in this state.
				Event::Disconnected | Event::PsmDrop | Event::PsmConnect => true,
				_ => false,
			},
			State::Outbound => match event {
				// Note: `Event::PsmConnect` must be ignored in this state.
				Event::Disconnected | Event::PsmDrop | Event::PsmConnect => true,
				_ => false,
			},
		}
	}
}

struct ControllerRunner {
	protocol_controller: ProtocolController,
	rx_finish: oneshot::Receiver<()>,
	tx_result: oneshot::Sender<Vec<(PeerId, Direction)>>,
}

struct ControllerRunnerHandle {
	tx_finish: oneshot::Sender<()>,
	rx_result: oneshot::Receiver<Vec<(PeerId, Direction)>>,
}

impl ControllerRunner {
	fn new(protocol_controller: ProtocolController) -> (ControllerRunner, ControllerRunnerHandle) {
		let (tx_finish, rx_finish) = oneshot::channel();
		let (tx_result, rx_result) = oneshot::channel();

		(
			ControllerRunner { protocol_controller, rx_finish, tx_result },
			ControllerRunnerHandle { tx_finish, rx_result },
		)
	}

	async fn run(mut self) {
		// Drive `ProtocolController` until we receive `rx_finish`.
		let mut finish = self.rx_finish.fuse();
		loop {
			// Note: the code below relies on the implementation detail that cancelling
			// `ProtocolController::next_action` is harmless.
			futures::select! {
				cont = self.protocol_controller.next_action().fuse() => {
					if !cont {
						panic!("`ProtocolController` has terminated.");
					}
				}
				_ = finish => {
					break
				}
			}
		}

		// It's time to consume all pending events. Drive `ProtocolController` until
		// it timeouts due to no pending events.
		loop {
			match tokio::time::timeout(
				Duration::from_millis(250),
				self.protocol_controller.next_action(),
			)
			.await
			{
				Ok(cont) =>
					if !cont {
						panic!("`ProtocolController` has terminated.");
					},
				Err(_) => break,
			}
		}

		// Send the resulting peer states.
		let _ = self.tx_result.send(
			self.protocol_controller
				.connected_peers()
				.map(|(peer_id, direction)| (*peer_id, *direction))
				.collect(),
		);
	}
}

impl ControllerRunnerHandle {
	async fn finish_and_receive_peer_states(self) -> Vec<(PeerId, Direction)> {
		let _ = self.tx_finish.send(());
		self.rx_result.await.unwrap()
	}
}

/// The main test fixture of the module.
struct ConnectionFuzzer {
	/// Nodes that we know about.
	known_nodes: HashMap<PeerId, State>,
	/// Nodes that we have reserved. Always a subset of `known_nodes`.
	reserved_nodes: HashSet<PeerId>,
	/// List of nodes we assume we are connected to. Always a subset of `known_nodes`.
	connected_nodes: HashSet<PeerId>,
	/// List of nodes in the `incoming` state that haven't been accepted or rejected yet.
	incoming_nodes: HashMap<IncomingIndex, PeerId>,
	/// Next id for incoming connections.
	next_incoming_id: IncomingIndex,
	/// Handle to `PeerStore`.
	peer_store_handle: PeerStoreHandle,
	/// `ProtocolController` handle.
	protocol_handle: ProtocolHandle,
	/// Protocol controller we are testing, behind `ControllerRunnerHandle`.
	runner_handle: Option<ControllerRunnerHandle>,
	/// Receiver of `ProtocolController` messages.
	from_controller: TracingUnboundedReceiver<Message>,
}

impl ConnectionFuzzer {
	/// Initialize the fuzzer.
	pub fn new() -> Self {
		let mut known_nodes = HashMap::<PeerId, State>::new();
		let mut reserved_nodes = HashSet::<PeerId>::new();

		// PRNG to use.
		let mut rng = rand::thread_rng();

		// Bootnodes for `PeerStore` initialization.
		let bootnodes = (0..Uniform::new_inclusive(0, 4).sample(&mut rng))
			.map(|_| {
				let id = PeerId::random();
				known_nodes.insert(id, State::Disconnected);
				id
			})
			.collect();

		let peer_store = PeerStore::new(bootnodes);
		let peer_store_handle = peer_store.handle();
		tokio::spawn(peer_store.run());

		let (to_notifications, from_controller) =
			tracing_unbounded("test_to_notifications", 10_000);
		let (protocol_handle, protocol_controller) = ProtocolController::new(
			SetId::from(0),
			ProtoSetConfig {
				reserved_nodes: {
					(0..Uniform::new_inclusive(0, 2).sample(&mut rng))
						.map(|_| {
							let id = PeerId::random();
							known_nodes.insert(id, State::Disconnected);
							reserved_nodes.insert(id);
							id
						})
						.collect()
				},
				in_peers: Uniform::new_inclusive(0, 25).sample(&mut rng),
				out_peers: Uniform::new_inclusive(0, 25).sample(&mut rng),
				reserved_only: Uniform::new_inclusive(0, 10).sample(&mut rng) == 0,
			},
			to_notifications,
			Box::new(peer_store_handle.clone()),
		);

		let (runner, runner_handle) = ControllerRunner::new(protocol_controller);
		tokio::spawn(runner.run());

		Self {
			known_nodes,
			reserved_nodes,
			connected_nodes: HashSet::<PeerId>::new(),
			incoming_nodes: HashMap::<IncomingIndex, PeerId>::new(),
			next_incoming_id: IncomingIndex(0),
			peer_store_handle,
			protocol_handle,
			runner_handle: Some(runner_handle),
			from_controller,
		}
	}

	pub async fn run(&mut self) {
		// Run fuzzing stage of the test.
		self.fuzz();

		// Make `ProtocolController` process remaining events and get peer states.
		let protocol_controller_nodes =
			self.runner_handle.take().unwrap().finish_and_receive_peer_states().await;

		// Process remaining messages from `ProtocolController`.
		self.process_remaining_messages();

		// Compare `ProtocolController` view of the peer states and our own.
		self.check_state_consistency(protocol_controller_nodes);
	}

	/// Ensure a valid event was received in this state.
	fn validate_state_transition(peer_id: PeerId, state: State, event: Event) {
		if !state.is_event_allowed(event) {
			panic!("Invalid state transition: {:?} x {:?} for peer {}", state, event, peer_id,);
		}
	}

	/// Returns `Some((peer, event, last_state))` if the message was processed, and `None`
	/// if it was ignored.
	fn handle_message(&mut self, message: Message) -> Option<(PeerId, State, Event)> {
		match message {
			Message::Connect { peer_id, .. } => {
				log::info!("PSM: connecting to peer {}", peer_id);

				let state = self.known_nodes.get_mut(&peer_id).unwrap();
				if matches!(*state, State::Incoming(_)) {
					log::info!(
						"Awaiting incoming response, ignoring obsolete Connect from PSM for peer {}",
						peer_id,
					);
					return None
				}

				let last_state = *state;

				if *state != State::Inbound {
					*state = State::Outbound;
				}

				if !self.connected_nodes.insert(peer_id) {
					log::info!("Request to connect to an already connected node {peer_id}");
				}

				Some((peer_id, last_state, Event::PsmConnect))
			},
			Message::Drop { peer_id, .. } => {
				log::info!("PSM: dropping peer {}", peer_id);

				let state = self.known_nodes.get_mut(&peer_id).unwrap();
				if matches!(*state, State::Incoming(_)) {
					log::info!(
						"Awaiting incoming response, ignoring obsolete Drop from PSM for peer {}",
						peer_id,
					);
					return None
				}

				let last_state = *state;
				*state = State::Disconnected;

				if !self.connected_nodes.remove(&peer_id) {
					log::info!("Ignoring attempt to drop a disconnected peer {}", peer_id);
				}

				Some((peer_id, last_state, Event::PsmDrop))
			},
			Message::Accept(n) => {
				log::info!("PSM: accepting index {}", n.0);

				let peer_id = self.incoming_nodes.remove(&n).unwrap();

				let state = self.known_nodes.get_mut(&peer_id).unwrap();
				match *state {
					State::Incoming(incoming_index) =>
						if n.0 < incoming_index.0 {
							log::info!(
								"Ignoring obsolete Accept for {:?} while awaiting {:?} for peer {}",
								n,
								incoming_index,
								peer_id,
							);
							return None
						} else if n.0 > incoming_index.0 {
							panic!(
								"Received {:?} while awaiting {:?} for peer {}",
								n, incoming_index, peer_id,
							);
						},
					_ => {},
				}

				let last_state = *state;
				*state = State::Inbound;

				assert!(self.connected_nodes.insert(peer_id));

				Some((peer_id, last_state, Event::PsmAccept))
			},
			Message::Reject(n) => {
				log::info!("PSM: rejecting index {}", n.0);

				let peer_id = self.incoming_nodes.remove(&n).unwrap();

				let state = self.known_nodes.get_mut(&peer_id).unwrap();
				match *state {
					State::Incoming(incoming_index) =>
						if n.0 < incoming_index.0 {
							log::info!(
								"Ignoring obsolete Reject for {:?} while awaiting {:?} for peer {}",
								n,
								incoming_index,
								peer_id,
							);
							return None
						} else if n.0 > incoming_index.0 {
							panic!(
								"Received {:?} while awaiting {:?} for peer {}",
								n, incoming_index, peer_id,
							);
						},
					_ => {},
				}

				let last_state = *state;
				*state = State::Disconnected;

				assert!(!self.connected_nodes.contains(&peer_id));

				Some((peer_id, last_state, Event::PsmReject))
			},
		}
	}

	fn fuzz(&mut self) {
		// PRNG to use in a `spawn_blocking` context.
		let mut rng = rand::thread_rng();

		// Perform a certain number of actions while checking that the state is consistent. If we
		// reach the end of the loop, the run has succeeded.
		// Note that with the ACKing and event postponing mechanism in `ProtocolController`
		// the test time grows quadratically with the number of iterations below.
		for _ in 0..10000 {
			// Peer we are working with.
			let mut current_peer = None;
			// Current event for state transition validation.
			let mut current_event = None;
			// Last peer state for allowed event validation.
			let mut last_state = None;

			// Each of these weights corresponds to an action that we may perform.
			let action_weights = [150, 90, 90, 30, 30, 1, 1, 4, 4];

			match WeightedIndex::new(&action_weights).unwrap().sample(&mut rng) {
				// If we generate 0, try to grab the next message from `ProtocolController`.
				0 => match self.from_controller.next().now_or_never() {
					Some(Some(message)) =>
						if let Some(result) = self.handle_message(message) {
							current_peer = Some(result.0);
							last_state = Some(result.1);
							current_event = Some(result.2);
						} else {
							continue
						},
					Some(None) => panic!("`ProtocolController` has terminated."),
					None => {},
				},

				// If we generate 1, discover a new node.
				1 => {
					let new_id = PeerId::random();
					self.known_nodes.insert(new_id, State::Disconnected);
					self.peer_store_handle.add_known_peer(new_id);
				},

				// If we generate 2, adjust a random reputation.
				2 =>
					if let Some(id) = self.known_nodes.keys().choose(&mut rng) {
						let val = Uniform::new_inclusive(i32::MIN, i32::MAX).sample(&mut rng);
						self.peer_store_handle.report_peer(*id, ReputationChange::new(val, ""));
					},

				// If we generate 3, disconnect from a random node.
				3 =>
					if let Some(id) = self.connected_nodes.iter().choose(&mut rng).cloned() {
						log::info!("Disconnected from {}", id);
						self.connected_nodes.remove(&id);

						let state = self.known_nodes.get_mut(&id).unwrap();
						last_state = Some(*state);
						*state = State::Disconnected;

						self.protocol_handle.dropped(id);

						current_peer = Some(id);
						current_event = Some(Event::Disconnected);
					},

				// If we generate 4, connect to a random node.
				4 => {
					if let Some(id) = self
						.known_nodes
						.keys()
						.filter(|n| {
							self.incoming_nodes.values().all(|m| m != *n) &&
								!self.connected_nodes.contains(*n)
						})
						.choose(&mut rng)
						.cloned()
					{
						log::info!(
							"Incoming connection from {}, index {}",
							id,
							self.next_incoming_id.0
						);
						self.protocol_handle.incoming_connection(id, self.next_incoming_id);
						self.incoming_nodes.insert(self.next_incoming_id, id);

						let state = self.known_nodes.get_mut(&id).unwrap();
						last_state = Some(*state);
						*state = State::Incoming(self.next_incoming_id);

						self.next_incoming_id.0 += 1;

						current_peer = Some(id);
						current_event = Some(Event::Incoming);
					}
				},

				// 5 and 6 are the reserved-only mode.
				5 => {
					log::info!("Set reserved only");
					self.protocol_handle.set_reserved_only(true);
				},
				6 => {
					log::info!("Unset reserved only");
					self.protocol_handle.set_reserved_only(false);
				},

				// 7 and 8 are about switching a random node in or out of reserved mode.
				7 => {
					if let Some(id) = self
						.known_nodes
						.keys()
						.filter(|n| !self.reserved_nodes.contains(*n))
						.choose(&mut rng)
					{
						log::info!("Add reserved: {}", id);
						self.protocol_handle.add_reserved_peer(*id);
						self.reserved_nodes.insert(*id);
					}
				},
				8 =>
					if let Some(id) = self.reserved_nodes.iter().choose(&mut rng).cloned() {
						log::info!("Remove reserved: {}", id);
						self.reserved_nodes.remove(&id);
						self.protocol_handle.remove_reserved_peer(id);
					},

				_ => unreachable!(),
			}

			// Validate state transitions.
			if let Some(peer_id) = current_peer {
				ConnectionFuzzer::validate_state_transition(
					peer_id,
					last_state.unwrap(),
					current_event.unwrap(),
				);
			}
		}
	}

	fn process_remaining_messages(&mut self) {
		// Validate remaining messages.
		while let Some(message) = self.from_controller.next().now_or_never() {
			if let Some(message) = message {
				if let Some(result) = self.handle_message(message) {
					let (peer_id, state, event) = result;
					ConnectionFuzzer::validate_state_transition(peer_id, state, event);
				} else {
					continue
				}
			} else {
				// End of `ProtocolController` message stream (we end up here
				// if `ControllerRunner::run` has already finished).
				break
			}
		}
	}

	fn check_state_consistency(&mut self, protocol_controller_nodes: Vec<(PeerId, Direction)>) {
		protocol_controller_nodes.iter().for_each(|(peer_id, direction)| {
			match self.known_nodes.remove(peer_id).unwrap() {
				State::Disconnected => panic!("State mismatch: {peer_id} is not connected."),
				State::Incoming(_) => panic!("State mismatch: {peer_id} is marked as incoming."),
				State::Inbound =>
					if !matches!(direction, Direction::Inbound) {
						panic!(
							"State mismatch: {peer_id} is connected via outbound instead of inbound."
						);
					},
				State::Outbound =>
					if !matches!(direction, Direction::Outbound) {
						panic!(
							"State mismatch: {peer_id} is connected via inbound instead of outbound."
						);
					},
			}
		});

		// Make sure only disconnected nodes are left.

		let mut more_nodes = false;
		self.known_nodes.iter().for_each(|(peer_id, state)| {
			if !matches!(state, State::Disconnected) {
				more_nodes = true;
				log::error!("{peer_id} is in state {state:?}.");
			}
		});

		assert!(!more_nodes, "States are not consistent, see error logs.")
	}
}

// We use two-threaded runtime, because `ConnectionFuzzer::run()` is mostly synchronous.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn run() {
	sp_tracing::try_init_simple();

	for _ in 0..50 {
		test_once().await;
	}
}

async fn test_once() {
	let mut fuzzer = ConnectionFuzzer::new();
	fuzzer.run().await;
}
