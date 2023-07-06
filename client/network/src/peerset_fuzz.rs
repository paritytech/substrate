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

use futures::prelude::*;
use libp2p::PeerId;
use rand::{
	distributions::{Distribution, Uniform, WeightedIndex},
	rngs::ThreadRng,
	seq::IteratorRandom,
};

use crate::{
	peerset::{
		DropReason, IncomingIndex, Message, Peerset, PeersetConfig, PeersetHandle,
		ReputationChange, SetConfig, SetId,
	},
	protocol_controller::Direction,
};

use std::{
	collections::{HashMap, HashSet},
	task::{Context, Poll},
};

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
	/// The peer set manager.
	peerset: Peerset,
	/// The handle to `Peerset`.
	peerset_handle: PeersetHandle,
	/// PRNG to use.
	rng: ThreadRng,
}

impl ConnectionFuzzer {
	/// Initialize the fuzzer.
	fn new() -> Self {
		let mut known_nodes = HashMap::<PeerId, State>::new();
		let mut reserved_nodes = HashSet::<PeerId>::new();

		// PRNG to use.
		let mut rng = rand::thread_rng();

		let (peerset, peerset_handle) = Peerset::from_config(PeersetConfig {
			sets: vec![SetConfig {
				bootnodes: (0..Uniform::new_inclusive(0, 4).sample(&mut rng))
					.map(|_| {
						let id = PeerId::random();
						known_nodes.insert(id, State::Disconnected);
						id
					})
					.collect(),
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
			}],
		});

		Self {
			known_nodes,
			reserved_nodes,
			connected_nodes: HashSet::<PeerId>::new(),
			incoming_nodes: HashMap::<IncomingIndex, PeerId>::new(),
			next_incoming_id: IncomingIndex(0),
			peerset,
			peerset_handle,
			rng,
		}
	}

	fn run(&mut self) {
		// Run fuzzing stage of the test.
		futures::executor::block_on(futures::future::poll_fn(|cx| {
			self.fuzz(cx);
			Poll::Ready(())
		}));

		// Process remaining messages from `Peerset`.
		futures::executor::block_on(futures::future::poll_fn(|cx| {
			self.process_remaining_messages(cx);
			Poll::Ready(())
		}));

		// Compare `Peerset` view of the peer states and our own.
		self.check_state_consistency(
			self.peerset.connected_peers(SetId::from(0)).map(|(p, d)| (*p, *d)).collect(),
		);
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

	fn fuzz(&mut self, cx: &mut Context) {
		// Perform a certain number of actions while checking that the state is consistent.
		for _ in 0..10000 {
			// Peer we are working with.
			let mut current_peer = None;
			// Current event for state transition validation.
			let mut current_event = None;
			// Last peer state for allowed event validation.
			let mut last_state = None;

			// Each of these weights corresponds to an action that we may perform.
			let action_weights = [150, 90, 90, 30, 30, 1, 1, 4, 4];

			match WeightedIndex::new(&action_weights).unwrap().sample(&mut self.rng) {
				// If we generate 0, poll `Peerset`.
				0 => match self.peerset.poll_next_unpin(cx) {
					Poll::Ready(Some(message)) =>
						if let Some(result) = self.handle_message(message) {
							current_peer = Some(result.0);
							last_state = Some(result.1);
							current_event = Some(result.2);
						} else {
							continue
						},
					Poll::Ready(None) => panic!("`Peerset` has terminated."),
					Poll::Pending => {},
				},

				// If we generate 1, discover a new node.
				1 => {
					let new_id = PeerId::random();
					self.known_nodes.insert(new_id, State::Disconnected);
					self.peerset_handle.add_known_peer(new_id);
				},

				// If we generate 2, adjust a random reputation.
				2 =>
					if let Some(id) = self.known_nodes.keys().choose(&mut self.rng) {
						let val = Uniform::new_inclusive(i32::MIN, i32::MAX).sample(&mut self.rng);
						self.peerset_handle.report_peer(*id, ReputationChange::new(val, ""));
					},

				// If we generate 3, disconnect from a random node.
				3 =>
					if let Some(id) = self.connected_nodes.iter().choose(&mut self.rng).cloned() {
						log::info!("Disconnected from {}", id);
						self.connected_nodes.remove(&id);

						let state = self.known_nodes.get_mut(&id).unwrap();
						last_state = Some(*state);
						*state = State::Disconnected;

						self.peerset.dropped(SetId::from(0), id, DropReason::Unknown);

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
						.choose(&mut self.rng)
						.cloned()
					{
						log::info!(
							"Incoming connection from {}, index {}",
							id,
							self.next_incoming_id.0
						);
						self.peerset.incoming(SetId::from(0), id, self.next_incoming_id);
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
					self.peerset_handle.set_reserved_only(SetId::from(0), true);
				},
				6 => {
					log::info!("Unset reserved only");
					self.peerset_handle.set_reserved_only(SetId::from(0), false);
				},

				// 7 and 8 are about switching a random node in or out of reserved mode.
				7 => {
					if let Some(id) = self
						.known_nodes
						.keys()
						.filter(|n| !self.reserved_nodes.contains(*n))
						.choose(&mut self.rng)
					{
						log::info!("Add reserved: {}", id);
						self.peerset_handle.add_reserved_peer(SetId::from(0), *id);
						self.reserved_nodes.insert(*id);
					}
				},
				8 =>
					if let Some(id) = self.reserved_nodes.iter().choose(&mut self.rng).cloned() {
						log::info!("Remove reserved: {}", id);
						self.reserved_nodes.remove(&id);
						self.peerset_handle.remove_reserved_peer(SetId::from(0), id);
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

	fn process_remaining_messages(&mut self, cx: &mut Context) {
		// Validate remaining messages.
		while let Poll::Ready(message) = self.peerset.poll_next_unpin(cx) {
			if let Some(message) = message {
				if let Some(result) = self.handle_message(message) {
					let (peer_id, state, event) = result;
					ConnectionFuzzer::validate_state_transition(peer_id, state, event);
				} else {
					continue
				}
			} else {
				panic!("`Peerset` has terminated.");
			}
		}
	}

	fn check_state_consistency(&mut self, peerset_nodes: Vec<(PeerId, Direction)>) {
		peerset_nodes.iter().for_each(|(peer_id, direction)| {
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
				log::error!("Untracked connection: {peer_id}, direction {state:?}).");
			}
		});

		assert!(!more_nodes, "States are not consistent, see error logs.")
	}
}

#[test]
fn run() {
	sp_tracing::try_init_simple();

	for _ in 0..50 {
		test_once();
	}
}

fn test_once() {
	let mut fuzzer = ConnectionFuzzer::new();
	fuzzer.run();
}
