use libp2p::PeerId;
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
	let mut index_to_peer = HashMap::new();

	let bootnode_index = IncomingIndex(0);
	actions.push((bootnode.clone(), TestAction::AddReservedPeer));
	actions.push((bootnode.clone(), TestAction::SetReservedOnly(true)));
	actions.push((bootnode.clone(), TestAction::ReportPeer(-1)));
	actions.push((bootnode.clone(), TestAction::SetReservedOnly(false)));
	actions.push((bootnode.clone(), TestAction::RemoveReservedPeer));
	actions.push((bootnode.clone(), TestAction::DropPeer));
	actions.push((bootnode.clone(), TestAction::Incoming(bootnode_index)));
	actions.push((bootnode.clone(), TestAction::Discovered(discovered.clone())));

	index_to_peer.insert(bootnode_index, bootnode.clone());
	discovered.push(bootnode.clone());

	for i in 1..150 {
		let peer_id = PeerId::random();
		let index = IncomingIndex(i);
		println!("Peer: {:?} {:?}", peer_id, index);
		index_to_peer.insert(index, peer_id.clone());
		discovered.push(peer_id.clone());
		if i > 75 {
			// Includes AddReservedPeer.
			actions.push((peer_id.clone(), TestAction::AddReservedPeer));
			actions.push((peer_id.clone(), TestAction::SetReservedOnly(true)));
			actions.push((peer_id.clone(), TestAction::ReportPeer(-1)));
			actions.push((peer_id.clone(), TestAction::SetReservedOnly(false)));
			actions.push((peer_id.clone(), TestAction::RemoveReservedPeer));
			actions.push((peer_id.clone(), TestAction::DropPeer));
			actions.push((peer_id.clone(), TestAction::Incoming(index)));
			actions.push((peer_id.clone(), TestAction::Discovered(discovered.clone())));
		} else {
			actions.push((peer_id.clone(), TestAction::SetReservedOnly(true)));
			actions.push((peer_id.clone(), TestAction::ReportPeer(-1)));
			actions.push((peer_id.clone(), TestAction::SetReservedOnly(false)));
			actions.push((peer_id.clone(), TestAction::RemoveReservedPeer));
			actions.push((peer_id.clone(), TestAction::DropPeer));
			actions.push((peer_id.clone(), TestAction::Incoming(index)));
			actions.push((peer_id.clone(), TestAction::Discovered(discovered.clone())));
		}
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

	let mut last_received_messages = HashMap::new();
	loop {
		let message = match next_message(peerset) {
			Ok((message, p)) => {
				println!("Message {:?}", message);
				peerset = p;
				message
			},
			_ => break,
		};
		match message {
			Message::Connect(peer_id) => {
				let last_message = last_received_messages.get(&peer_id);
				match last_message {
					Some(Message::Drop(_)) | Some(Message::Reject(_)) => {},
					_ => {
						let relevant_api_called = dropped_called.remove(&peer_id) || discovered_called.remove(&peer_id);
						if !relevant_api_called && !(peer_id == bootnode) {
							panic!("Unexpected Connect message after a {:?} message", last_message);
						}
					},
				}
				last_received_messages.insert(peer_id.clone(), Message::Connect(peer_id));
			},
			Message::Drop(peer_id) => {
				let maybe_related_action = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						actions.pop_front()
					} else {
						None
					}
				};
				let last_message = last_received_messages.get(&peer_id);
				match last_message {
					Some(Message::Connect(_)) | Some(Message::Accept(_)) => {},
					_ => panic!("Unexpected Drop message, after a {:?} message, a perhaps related action was: {:?}", last_message, maybe_related_action),
				}
				last_received_messages.insert(peer_id.clone(), Message::Drop(peer_id));
			},
			Message::Accept(index) => {
				let peer_id = index_to_peer.get(&index).expect("Unknown index");
				println!("ID: {:?}", peer_id);
				if let Some(Message::Connect(_)) = last_received_messages.get(&peer_id) {
					panic!("Unexpected Accept message, after a Connect message");
				}
				last_received_messages.insert(peer_id.clone(), Message::Accept(index));
			},
			Message::Reject(index) => {
				let peer_id = index_to_peer.get(&index).expect("Unknown index");
				if let Some(Message::Connect(_)) = last_received_messages.get(&peer_id) {
					panic!("Unexpected Reject message, after a Connect message");
				}
				last_received_messages.insert(peer_id.clone(), Message::Reject(index));
			},
		}
	}
}
