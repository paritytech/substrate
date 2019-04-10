use libp2p::PeerId;
use futures::prelude::*;
use rand::thread_rng;
use rand::seq::SliceRandom;
use super::{PeersetConfig, Peerset, Message, IncomingIndex, next_message};
use std::collections::{HashMap, HashSet, VecDeque};

#[test]
fn test_random_api_use() {

	#[derive(Debug)]
	enum TestAction {
		AddReservedPeer,
		RemoveReservedPeer,
		SetReservedOnly(bool),
		ReportPeer(i32),
		DropPeer,
		Incoming(IncomingIndex),
		Discovered(Vec<PeerId>),
	}

	let bootnode = PeerId::random();
	let config = PeersetConfig {
		in_peers: 100,
		out_peers: 100,
		bootnodes: vec![bootnode.clone()],
		reserved_only: false,
		reserved_nodes: Vec::new(),
	};

	let (mut peerset, handle) = Peerset::from_config(config);

	let mut actions = vec![];
	let mut discovered = vec![];
	discovered.push(bootnode.clone());

	actions.push((bootnode.clone(), TestAction::AddReservedPeer));
	actions.push((bootnode.clone(), TestAction::SetReservedOnly(true)));
	actions.push((bootnode.clone(), TestAction::ReportPeer(-1)));
	actions.push((bootnode.clone(), TestAction::SetReservedOnly(false)));
	actions.push((bootnode.clone(), TestAction::RemoveReservedPeer));
	actions.push((bootnode.clone(), TestAction::DropPeer));
	actions.push((bootnode.clone(), TestAction::Incoming(IncomingIndex(1))));
	actions.push((bootnode.clone(), TestAction::Discovered(discovered.clone())));

	for i in 0..125 {
		let peer_id = PeerId::random();
		discovered.push(peer_id.clone());
		actions.push((peer_id.clone(), TestAction::AddReservedPeer));
		actions.push((peer_id.clone(), TestAction::SetReservedOnly(true)));
		actions.push((peer_id.clone(), TestAction::ReportPeer(-1)));
		actions.push((peer_id.clone(), TestAction::SetReservedOnly(false)));
		actions.push((peer_id.clone(), TestAction::RemoveReservedPeer));
		actions.push((peer_id.clone(), TestAction::DropPeer));
		actions.push((peer_id.clone(), TestAction::Incoming(IncomingIndex(i))));
		actions.push((peer_id.clone(), TestAction::Discovered(discovered.clone())));
	}

	for _ in 0..25 {
		// Actions for peers that do not include a AddReservedPeer.
		let peer_id = PeerId::random();
		discovered.push(peer_id.clone());
		actions.push((peer_id.clone(), TestAction::ReportPeer(-1)));
		actions.push((peer_id.clone(), TestAction::RemoveReservedPeer));
		actions.push((peer_id.clone(), TestAction::DropPeer));
		actions.push((peer_id.clone(), TestAction::Discovered(discovered.clone())));
	}

	let mut dropped_called = HashSet::new();
	let mut discovered_called = HashSet::new();
	let mut performed_actions = HashMap::new();

	let mut rng = thread_rng();
	for (peer_id, action) in actions.choose_multiple(&mut rng, actions.len()) {
		match action {
			TestAction::AddReservedPeer => {
				handle.add_reserved_peer(peer_id.clone());
			},
			TestAction::RemoveReservedPeer => {
				handle.remove_reserved_peer(peer_id.clone());
			},
			TestAction::SetReservedOnly(reserved) => {
				handle.set_reserved_only(reserved.clone());
			},
			TestAction::ReportPeer(diff_score) => {
				handle.report_peer(peer_id.clone(), diff_score.clone());
			},
			TestAction::DropPeer => {
				peerset.dropped(peer_id.clone());
				dropped_called.insert(peer_id.clone());
			},
			TestAction::Incoming(index) => {
				peerset.incoming(peer_id.clone(), index.clone());
			},
			TestAction::Discovered(nodes) => {
				peerset.discovered(nodes.clone());
				for node in nodes {
					discovered_called.insert(node.clone());
				}
			},
		}
		let performed = performed_actions
			.entry(peer_id.clone())
			.or_insert(VecDeque::new());
		performed.push_back(action)
	}

	drop(handle);

	let mut last_connected_messages = HashMap::new();
	let mut last_unconnected_messages = HashMap::new();
	loop {
		let message = match next_message(peerset) {
			Ok((message, p)) => {
				peerset = p;
				message
			},
			_ => break,
		};
		match message {
			Message::Connect(peer_id) => {
				let last_message = last_connected_messages.get(&peer_id);
				match last_message {
					Some(Message::Drop(_)) => {},
					_ => {
						let relevant_api_called = dropped_called.remove(&peer_id) || discovered_called.remove(&peer_id);
						if !relevant_api_called && !(peer_id == bootnode) && !last_unconnected_messages.len() > 0 {
							panic!("Unexpected Connect message after a {:?} message", last_message);
						}
					},
				}
				last_connected_messages.insert(peer_id.clone(), Message::Connect(peer_id));
			},
			Message::Drop(peer_id) => {
				let maybe_related_action = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						actions.pop_front()
					} else {
						None
					}
				};
				let last_message = last_connected_messages.get(&peer_id);
				match last_message {
					Some(Message::Connect(_)) => {},
					_ => {
						if !last_unconnected_messages.len() > 0 {
							panic!("Unexpected Drop message, after a {:?} message, a perhaps related action was: {:?}", last_message, maybe_related_action);
						}
					},
				}
				last_connected_messages.insert(peer_id.clone(), Message::Drop(peer_id));
			},
			Message::Accept(index) => {
				if let Some(last_message) = last_unconnected_messages.get(&index) {
					match last_message {
						// Note: this will never hit, since Connect messages are stored by peer_id in last_connected_message...
						Message::Connect(_) => panic!("Unexpected Accept message, after a Connect message"),
						_ => {},
					}
				}
				last_unconnected_messages.insert(index.clone(), Message::Accept(index));
			},
			Message::Reject(index) => {
				if let Some(last_message) = last_unconnected_messages.get(&index) {
					match last_message {
						// Note: this will never hit, since Connect messages are stored by peer_id in last_connected_message...
						Message::Connect(_) => panic!("Unexpected Reject message, after a Connect message"),
						_ => {},
					}
				}
				last_unconnected_messages.insert(index.clone(), Message::Reject(index));
			},
		}
	}
}
