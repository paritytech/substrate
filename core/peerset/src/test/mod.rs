use libp2p::PeerId;
use rand::thread_rng;
use rand::seq::SliceRandom;
use super::{PeersetConfig, Peerset, Message, IncomingIndex, next_message};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{self, Debug};

#[test]
fn test_random_api_use() {

    #[derive(Eq, PartialEq)]
	enum TestAction {
		AddReservedPeer,
		RemoveReservedPeer,
		SetReservedOnly(bool),
		ReportPeer(i32),
		DropPeer,
		Incoming(IncomingIndex),
		Discovered(Vec<PeerId>),
	}

	impl Debug for TestAction {
	    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
	        match self {
				TestAction::AddReservedPeer => {
					write!(f, "AddReservedPeer")
				},
				TestAction::RemoveReservedPeer => {
					write!(f, "RemoveReservedPeer")
				},
				TestAction::SetReservedOnly(reserved) => {
					write!(f, "SetReservedOnly {:?}", reserved)
				},
				TestAction::ReportPeer(diff_score) => {
					write!(f, "ReportPeer {:?}", diff_score)
				},
				TestAction::DropPeer => {
					write!(f, "DropPeer")
				},
				TestAction::Incoming(index) => {
					write!(f, "Incoming {:?}", index)
				},
				TestAction::Discovered(nodes) => {
					write!(f, "Discovered {:?}", nodes.len())
				},
	        }
	    }
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

	let mut last_received_messages: HashMap<PeerId, VecDeque<Message>> = HashMap::new();
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
				let last_message = {
                    if let Some(messages) = last_received_messages.get_mut(&peer_id) {
                        messages.pop_front()
                    } else {
                        None
                    }
                };
				let action_sequence = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						Some(actions.clone())
					} else {
						None
					}
				};
				match last_message {
					Some(Message::Drop(_)) | Some(Message::Reject(_)) => {},
					_ => {
						let relevant_api_called = dropped_called.remove(&peer_id) || discovered_called.remove(&peer_id);
						if !relevant_api_called && !(peer_id == bootnode) {
							panic!("Unexpected Connect message after a {:?} message, sequence of actions: {:?}", last_message, action_sequence);
						}
					},
				}
				let received = last_received_messages.entry(peer_id.clone()).or_insert(VecDeque::new());
                received.push_back(Message::Connect(peer_id));
			},
			Message::Drop(peer_id) => {
				let action_sequence = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						Some(actions.clone())
					} else {
						None
					}
				};
				let last_message = {
                    if let Some(messages) = last_received_messages.get_mut(&peer_id) {
                        messages.pop_front()
                    } else {
                        None
                    }
                };
				match last_message {
					Some(Message::Connect(_)) | Some(Message::Accept(_)) => {},
					_ => panic!("Unexpected Drop message, after a {:?} message, sequence of actions: {:?}", last_message, action_sequence),
				}
				let received = last_received_messages.entry(peer_id.clone()).or_insert(VecDeque::new());
                received.push_back(Message::Drop(peer_id));
			},
			Message::Accept(index) => {
				let peer_id = index_to_peer.get(&index).expect("Unknown index");
				let action_sequence = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						Some(actions.clone())
					} else {
						None
					}
				};
				let last_messages = {
                    if let Some(messages) = last_received_messages.get_mut(&peer_id) {
                        messages
                    } else {
                        continue;
                    }
                };
				if let Some(Message::Connect(_)) = last_messages.pop_front() {
                    if let Some(action_sequence) = action_sequence.clone() {
                        let mut actions = action_sequence.into_iter();
                        let drop_position = actions.clone().rposition(|x| x == &TestAction::DropPeer);
                        let incoming_position = actions.rposition(|x| x == &TestAction::Incoming(index));
                        match (drop_position, incoming_position) {
                            (Some(drop), Some(incoming)) => {
                                assert!(drop < incoming);
                                println!("Last messages: {:?}", last_messages);
                                assert!(last_messages.contains(&Message::Connect(peer_id.clone())));
                                continue
                            },
                            _ => {}
                        }
                    }
					panic!("Unexpected Accept message, after a Connect message, sequence of actions: {:?}", action_sequence);
				}
				let received = last_received_messages.entry(peer_id.clone()).or_insert(VecDeque::new());
                received.push_back(Message::Accept(index));
			},
			Message::Reject(index) => {
				let peer_id = index_to_peer.get(&index).expect("Unknown index");
				let action_sequence = {
					if let Some(actions) = performed_actions.get_mut(&peer_id) {
						Some(actions.clone())
					} else {
						None
					}
				};
				let last_messages = {
                    if let Some(messages) = last_received_messages.get_mut(&peer_id) {
                        messages
                    } else {
                        continue;
                    }
                };
				if let Some(Message::Connect(_)) = last_messages.pop_front() {
					panic!("Unexpected Reject message, after a Connect message, sequence of actions: {:?}", action_sequence);
				}
				let received = last_received_messages.entry(peer_id.clone()).or_insert(VecDeque::new());
                received.push_back(Message::Reject(index));
			},
		}
	}
}
