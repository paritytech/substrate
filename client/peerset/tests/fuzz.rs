// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use futures::prelude::*;
use libp2p::PeerId;
use rand::distributions::{Distribution, Uniform, WeightedIndex};
use rand::seq::IteratorRandom;
use std::{collections::HashMap, collections::HashSet, iter, pin::Pin, task::Poll};
use sc_peerset::{IncomingIndex, Message, PeersetConfig, Peerset, ReputationChange};

#[test]
fn run() {
	for _ in 0..50 {
		test_once();
	}
}

fn test_once() {
	// PRNG to use.
	let mut rng = rand::thread_rng();

	// Nodes that the peerset knows about.
	let mut known_nodes = HashSet::<PeerId>::new();
	// Nodes that we have reserved. Always a subset of `known_nodes`.
	let mut reserved_nodes = HashSet::<PeerId>::new();

	let (mut peerset, peerset_handle) = Peerset::from_config(PeersetConfig {
		bootnodes: (0 .. Uniform::new_inclusive(0, 4).sample(&mut rng)).map(|_| {
			let id = PeerId::random();
			known_nodes.insert(id.clone());
			id
		}).collect(),
		priority_groups: {
			let list = (0 .. Uniform::new_inclusive(0, 2).sample(&mut rng)).map(|_| {
				let id = PeerId::random();
				known_nodes.insert(id.clone());
				reserved_nodes.insert(id.clone());
				id
			}).collect();
			vec![("reserved".to_owned(), list)]
		},
		reserved_only: Uniform::new_inclusive(0, 10).sample(&mut rng) == 0,
		in_peers: Uniform::new_inclusive(0, 25).sample(&mut rng),
		out_peers: Uniform::new_inclusive(0, 25).sample(&mut rng),
	});

	futures::executor::block_on(futures::future::poll_fn(move |cx| {
		// List of nodes the user of `peerset` assumes it's connected to. Always a subset of
		// `known_nodes`.
		let mut connected_nodes = HashSet::<PeerId>::new();
		// List of nodes the user of `peerset` called `incoming` with and that haven't been
		// accepted or rejected yet.
		let mut incoming_nodes = HashMap::<IncomingIndex, PeerId>::new();
		// Next id for incoming connections.
		let mut next_incoming_id = IncomingIndex(0);

		// Perform a certain number of actions while checking that the state is consistent. If we
		// reach the end of the loop, the run has succeeded.
		for _ in 0 .. 2500 {
			// Each of these weights corresponds to an action that we may perform.
			let action_weights = [150, 90, 90, 30, 30, 1, 1, 4, 4];
			match WeightedIndex::new(&action_weights).unwrap().sample(&mut rng) {
				// If we generate 0, poll the peerset.
				0 => match Stream::poll_next(Pin::new(&mut peerset), cx) {
					Poll::Ready(Some(Message::Connect(id))) => {
						if let Some(id) = incoming_nodes.iter().find(|(_, v)| **v == id).map(|(&id, _)| id) {
							incoming_nodes.remove(&id);
						}
						assert!(connected_nodes.insert(id));
					}
					Poll::Ready(Some(Message::Drop(id))) => { connected_nodes.remove(&id); }
					Poll::Ready(Some(Message::Accept(n))) =>
						assert!(connected_nodes.insert(incoming_nodes.remove(&n).unwrap())),
					Poll::Ready(Some(Message::Reject(n))) =>
						assert!(!connected_nodes.contains(&incoming_nodes.remove(&n).unwrap())),
					Poll::Ready(None) => panic!(),
					Poll::Pending => {}
				}

				// If we generate 1, discover a new node.
				1 => {
					let new_id = PeerId::random();
					known_nodes.insert(new_id.clone());
					peerset.discovered(iter::once(new_id));
				}

				// If we generate 2, adjust a random reputation.
				2 => if let Some(id) = known_nodes.iter().choose(&mut rng) {
					let val = Uniform::new_inclusive(i32::min_value(), i32::max_value()).sample(&mut rng);
					peerset_handle.report_peer(id.clone(), ReputationChange::new(val, ""));
				}

				// If we generate 3, disconnect from a random node.
				3 => if let Some(id) = connected_nodes.iter().choose(&mut rng).cloned() {
					connected_nodes.remove(&id);
					peerset.dropped(id);
				}

				// If we generate 4, connect to a random node.
				4 => if let Some(id) = known_nodes.iter()
					.filter(|n| incoming_nodes.values().all(|m| m != *n) && !connected_nodes.contains(*n))
					.choose(&mut rng) {
					peerset.incoming(id.clone(), next_incoming_id.clone());
					incoming_nodes.insert(next_incoming_id.clone(), id.clone());
					next_incoming_id.0 += 1;
				}

				// 5 and 6 are the reserved-only mode.
				5 => peerset_handle.set_reserved_only(true),
				6 => peerset_handle.set_reserved_only(false),

				// 7 and 8 are about switching a random node in or out of reserved mode.
				7 => if let Some(id) = known_nodes.iter().filter(|n| !reserved_nodes.contains(*n)).choose(&mut rng) {
					peerset_handle.add_reserved_peer(id.clone());
					reserved_nodes.insert(id.clone());
				}
				8 => if let Some(id) = reserved_nodes.iter().choose(&mut rng).cloned() {
					reserved_nodes.remove(&id);
					peerset_handle.remove_reserved_peer(id);
				}

				_ => unreachable!()
			}
		}

		Poll::Ready(())
	}));
}
