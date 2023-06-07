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

use futures::prelude::*;
use libp2p::PeerId;
use rand::{
	distributions::{Distribution, Uniform, WeightedIndex},
	seq::IteratorRandom,
};
use sc_network::{
	peer_store::{PeerStore, PeerStoreProvider},
	protocol_controller::{IncomingIndex, Message, ProtoSetConfig, ProtocolController, SetId},
	ReputationChange,
};
use sc_utils::mpsc::tracing_unbounded;
use std::collections::{HashMap, HashSet};

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

/// Bare simplified state without incoming index.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
enum BareState {
	/// Peer is not connected.
	Disconnected,
	/// We have an inbound connection, but have not decided yet whether to accept it.
	Incoming,
	/// Peer is connected via an inbound connection.
	Inbound,
	/// Peer is connected via an outbound connection.
	Outbound,
}

fn discard_incoming_index(state: State) -> BareState {
	match state {
		State::Disconnected => BareState::Disconnected,
		State::Incoming(_) => BareState::Incoming,
		State::Inbound => BareState::Inbound,
		State::Outbound => BareState::Outbound,
	}
}

#[tokio::test]
async fn run() {
	sp_tracing::try_init_simple();

	for _ in 0..50 {
		test_once().await;
	}
}

async fn test_once() {
	// Allowed events that can be received in a specific state.
	let allowed_events: HashMap<BareState, HashSet<Event>> = [
		(
			BareState::Disconnected,
			[Event::Incoming, Event::PsmConnect, Event::PsmDrop /* must be ignored */]
				.into_iter()
				.collect::<HashSet<_>>(),
		),
		(
			BareState::Incoming,
			[Event::PsmAccept, Event::PsmReject].into_iter().collect::<HashSet<_>>(),
		),
		(
			BareState::Inbound,
			[Event::Disconnected, Event::PsmDrop, Event::PsmConnect /* must be ignored */]
				.into_iter()
				.collect::<HashSet<_>>(),
		),
		(
			BareState::Outbound,
			[Event::Disconnected, Event::PsmDrop, Event::PsmConnect /* must be ignored */]
				.into_iter()
				.collect::<HashSet<_>>(),
		),
	]
	.into_iter()
	.collect();

	// PRNG to use.
	let mut rng = rand::thread_rng();

	// Nodes that the peerset knows about.
	let mut known_nodes = HashMap::<PeerId, State>::new();
	// Nodes that we have reserved. Always a subset of `known_nodes`.
	let mut reserved_nodes = HashSet::<PeerId>::new();

	// Bootnodes for `PeerStore` initialization.
	let bootnodes = (0..Uniform::new_inclusive(0, 4).sample(&mut rng))
		.map(|_| {
			let id = PeerId::random();
			known_nodes.insert(id, State::Disconnected);
			id
		})
		.collect();

	let peer_store = PeerStore::new(bootnodes);
	let mut peer_store_handle = peer_store.handle();

	let (to_notifications, mut from_controller) =
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

	tokio::spawn(peer_store.run());
	tokio::spawn(protocol_controller.run());

	// List of nodes the user of `peerset` assumes it's connected to. Always a subset of
	// `known_nodes`.
	let mut connected_nodes = HashSet::<PeerId>::new();
	// List of nodes the user of `peerset` called `incoming` with and that haven't been
	// accepted or rejected yet.
	let mut incoming_nodes = HashMap::<IncomingIndex, PeerId>::new();
	// Next id for incoming connections.
	let mut next_incoming_id = IncomingIndex(0);

	// The loop below is effectively synchronous, so for `PeerStore` & `ProtocolController`
	// runners, spawned above, to advance, we use `spawn_blocking`.
	let _ = tokio::task::spawn_blocking(move || {
		// PRNG to use in `spawn_blocking` context.
		let mut rng = rand::thread_rng();

		// Perform a certain number of actions while checking that the state is consistent. If we
		// reach the end of the loop, the run has succeeded.
		// Note that with the ACKing and event postponing mechanism in `ProtocolController`
		// the test time grows quadratically with the number of iterations below.
		for _ in 0..2500 {
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
				0 => match from_controller.next().now_or_never() {
					Some(Some(Message::Connect { peer_id, .. })) => {
						log::info!("PSM: connecting to peer {}", peer_id);

						let state = known_nodes.get_mut(&peer_id).unwrap();
						if matches!(*state, State::Incoming(_)) {
							log::info!(
								"Awaiting incoming response, ignoring obsolete Connect from PSM for peer {}",
								peer_id,
							);
							continue
						}

						last_state = Some(*state);

						if *state != State::Inbound {
							*state = State::Outbound;
						}

						if !connected_nodes.insert(peer_id) {
							log::info!("Request to connect to an already connected node {peer_id}");
						}

						current_peer = Some(peer_id);
						current_event = Some(Event::PsmConnect);
					},
					Some(Some(Message::Drop { peer_id, .. })) => {
						log::info!("PSM: dropping peer {}", peer_id);

						let state = known_nodes.get_mut(&peer_id).unwrap();
						if matches!(*state, State::Incoming(_)) {
							log::info!(
								"Awaiting incoming response, ignoring obsolete Drop from PSM for peer {}",
								peer_id,
							);
							continue
						}

						last_state = Some(*state);
						*state = State::Disconnected;

						if !connected_nodes.remove(&peer_id) {
							log::info!("Ignoring attempt to drop a disconnected peer {}", peer_id);
						}

						current_peer = Some(peer_id);
						current_event = Some(Event::PsmDrop);
					},
					Some(Some(Message::Accept(n))) => {
						log::info!("PSM: accepting index {}", n.0);

						let peer_id = incoming_nodes.remove(&n).unwrap();

						let state = known_nodes.get_mut(&peer_id).unwrap();
						match *state {
							State::Incoming(incoming_index) =>
								if n.0 < incoming_index.0 {
									log::info!(
										"Ignoring obsolete Accept for {:?} while awaiting {:?} for peer {}",
										n, incoming_index, peer_id,
									);
									continue
								} else if n.0 > incoming_index.0 {
									panic!(
										"Received {:?} while awaiting {:?} for peer {}",
										n, incoming_index, peer_id,
									);
								},
							_ => {},
						}

						last_state = Some(*state);
						*state = State::Inbound;

						assert!(connected_nodes.insert(peer_id));

						current_peer = Some(peer_id);
						current_event = Some(Event::PsmAccept);
					},
					Some(Some(Message::Reject(n))) => {
						log::info!("PSM: rejecting index {}", n.0);

						let peer_id = incoming_nodes.remove(&n).unwrap();

						let state = known_nodes.get_mut(&peer_id).unwrap();
						match *state {
							State::Incoming(incoming_index) =>
								if n.0 < incoming_index.0 {
									log::info!(
										"Ignoring obsolete Reject for {:?} while awaiting {:?} for peer {}",
										n, incoming_index, peer_id,
									);
									continue
								} else if n.0 > incoming_index.0 {
									panic!(
										"Received {:?} while awaiting {:?} for peer {}",
										n, incoming_index, peer_id,
									);
								},
							_ => {},
						}

						last_state = Some(*state);
						*state = State::Disconnected;

						assert!(!connected_nodes.contains(&peer_id));

						current_peer = Some(peer_id);
						current_event = Some(Event::PsmReject);
					},
					Some(None) => panic!(),
					None => {},
				},

				// If we generate 1, discover a new node.
				1 => {
					let new_id = PeerId::random();
					known_nodes.insert(new_id, State::Disconnected);
					peer_store_handle.add_known_peer(new_id);
				},

				// If we generate 2, adjust a random reputation.
				2 =>
					if let Some(id) = known_nodes.keys().choose(&mut rng) {
						let val = Uniform::new_inclusive(i32::MIN, i32::MAX).sample(&mut rng);
						peer_store_handle.report_peer(*id, ReputationChange::new(val, ""));
					},

				// If we generate 3, disconnect from a random node.
				3 =>
					if let Some(id) = connected_nodes.iter().choose(&mut rng).cloned() {
						log::info!("Disconnected from {}", id);
						connected_nodes.remove(&id);

						let state = known_nodes.get_mut(&id).unwrap();
						last_state = Some(*state);
						*state = State::Disconnected;

						protocol_handle.dropped(id);

						current_peer = Some(id);
						current_event = Some(Event::Disconnected);
					},

				// If we generate 4, connect to a random node.
				4 => {
					if let Some(id) = known_nodes
						.keys()
						.filter(|n| {
							incoming_nodes.values().all(|m| m != *n) &&
								!connected_nodes.contains(*n)
						})
						.choose(&mut rng)
						.cloned()
					{
						log::info!("Incoming connection from {}, index {}", id, next_incoming_id.0);
						protocol_handle.incoming_connection(id, next_incoming_id);
						incoming_nodes.insert(next_incoming_id, id);

						let state = known_nodes.get_mut(&id).unwrap();
						last_state = Some(*state);
						*state = State::Incoming(next_incoming_id);

						next_incoming_id.0 += 1;

						current_peer = Some(id);
						current_event = Some(Event::Incoming);
					}
				},

				// 5 and 6 are the reserved-only mode.
				5 => {
					log::info!("Set reserved only");
					protocol_handle.set_reserved_only(true);
				},
				6 => {
					log::info!("Unset reserved only");
					protocol_handle.set_reserved_only(false);
				},

				// 7 and 8 are about switching a random node in or out of reserved mode.
				7 => {
					if let Some(id) =
						known_nodes.keys().filter(|n| !reserved_nodes.contains(*n)).choose(&mut rng)
					{
						log::info!("Add reserved: {}", id);
						protocol_handle.add_reserved_peer(*id);
						reserved_nodes.insert(*id);
					}
				},
				8 =>
					if let Some(id) = reserved_nodes.iter().choose(&mut rng).cloned() {
						log::info!("Remove reserved: {}", id);
						reserved_nodes.remove(&id);
						protocol_handle.remove_reserved_peer(id);
					},

				_ => unreachable!(),
			}

			// Validate state transitions.
			if let Some(peer_id) = current_peer {
				let event = current_event.unwrap();
				let last_state = discard_incoming_index(last_state.unwrap());
				if !allowed_events.get(&last_state).unwrap().contains(&event) {
					panic!(
						"Invalid state transition: {:?} x {:?} for peer {}",
						last_state, event, peer_id,
					);
				}
			}
		}
	})
	.await;
}
