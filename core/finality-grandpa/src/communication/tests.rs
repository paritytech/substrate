// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Tests for the communication portion of the GRANDPA crate.

use futures::sync::mpsc;
use futures::prelude::*;
use network::consensus_gossip as network_gossip;
use network::test::{Block, Hash};
use network_gossip::Validator;
use tokio::runtime::current_thread;
use std::sync::Arc;
use keyring::AuthorityKeyring;
use parity_codec::Encode;

use super::gossip::{self, GossipValidator};
use super::{AuthorityId, VoterSet, Round, SetId};

enum Event {
	MessagesFor(Hash, mpsc::UnboundedSender<network_gossip::TopicNotification>),
	RegisterValidator(Arc<dyn network_gossip::Validator<Block>>),
	GossipMessage(Hash, Vec<u8>, bool),
	SendMessage(Vec<network::PeerId>, Vec<u8>),
	Report(network::PeerId, i32),
	Announce(Hash),
}

#[derive(Clone)]
struct TestNetwork {
	sender: mpsc::UnboundedSender<Event>,
}

impl super::Network<Block> for TestNetwork {
	type In = mpsc::UnboundedReceiver<network_gossip::TopicNotification>;

	/// Get a stream of messages for a specific gossip topic.
	fn messages_for(&self, topic: Hash) -> Self::In {
		let (tx, rx) = mpsc::unbounded();
		let _ = self.sender.unbounded_send(Event::MessagesFor(topic, tx));

		rx
	}

	/// Register a gossip validator.
	fn register_validator(&self, validator: Arc<dyn network_gossip::Validator<Block>>) {
		let _ = self.sender.unbounded_send(Event::RegisterValidator(validator));
	}

	/// Gossip a message out to all connected peers.
	///
	/// Force causes it to be sent to all peers, even if they've seen it already.
	/// Only should be used in case of consensus stall.
	fn gossip_message(&self, topic: Hash, data: Vec<u8>, force: bool) {
		let _ = self.sender.unbounded_send(Event::GossipMessage(topic, data, force));
	}

	/// Send a message to a bunch of specific peers, even if they've seen it already.
	fn send_message(&self, who: Vec<network::PeerId>, data: Vec<u8>) {
		let _ = self.sender.unbounded_send(Event::SendMessage(who, data));
	}

	/// Report a peer's cost or benefit after some action.
	fn report(&self, who: network::PeerId, cost_benefit: i32) {
		let _ = self.sender.unbounded_send(Event::Report(who, cost_benefit));
	}

	/// Inform peers that a block with given hash should be downloaded.
	fn announce(&self, block: Hash) {
		let _ = self.sender.unbounded_send(Event::Announce(block));
	}
}

struct Tester {
	net_handle: super::NetworkBridge<Block, TestNetwork>,
	gossip_validator: Arc<GossipValidator<Block>>,
	events: mpsc::UnboundedReceiver<Event>,
}

impl Tester {
	fn filter_network_events<F>(self, mut pred: F) -> impl Future<Item=Self,Error=()>
		where F: FnMut(Event) -> bool
	{
		let mut s = Some(self);
		futures::future::poll_fn(move || loop {
			match s.as_mut().unwrap().events.poll().expect("concluded early") {
				Async::Ready(None) => panic!("concluded early"),
				Async::Ready(Some(item)) => if pred(item) {
					return Ok(Async::Ready(s.take().unwrap()))
				},
				Async::NotReady => return Ok(Async::NotReady),
			}
		})
	}
}

// some random config (not really needed)
fn config() -> crate::Config {
	crate::Config {
		gossip_duration: std::time::Duration::from_millis(10),
		justification_period: 256,
		local_key: None,
		name: None,
	}
}

// needs to run in a tokio runtime.
fn make_test_network() -> impl Future<Item=Tester,Error=()> {
	let (tx, rx) = mpsc::unbounded();
	let net = TestNetwork { sender: tx };

	#[derive(Clone)]
	struct Exit;

	impl Future for Exit {
		type Item = ();
		type Error = ();

		fn poll(&mut self) -> Poll<(), ()> {
			Ok(Async::NotReady)
		}
	}

	let (bridge, startup_work) = super::NetworkBridge::new(
		net.clone(),
		config(),
		Exit,
	);

	startup_work.map(move |()| Tester {
		gossip_validator: bridge.validator.clone(),
		net_handle: bridge,
		events: rx,
	})
}

fn make_ids(keys: &[AuthorityKeyring]) -> Vec<(AuthorityId, u64)> {
	keys.iter()
		.map(|key| AuthorityId(key.to_raw_public()))
		.map(|id| (id, 1))
		.collect()
}

struct NoopContext;

impl network_gossip::ValidatorContext<Block> for NoopContext {
	fn broadcast_topic(&mut self, _: Hash, _: bool) { }
	fn broadcast_message(&mut self, _: Hash, _: Vec<u8>, _: bool) { }
	fn send_message(&mut self, _: &network::PeerId, _: Vec<u8>) { }
	fn send_topic(&mut self, _: &network::PeerId, _: Hash, _: bool) { }
}

#[test]
fn good_commit_leads_to_relay() {
	let private = [AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let public = make_ids(&private[..]);
	let voter_set = Arc::new(public.iter().cloned().collect::<VoterSet<AuthorityId>>());

	let round = 0;
	let set_id = 1;

	let commit = {
		let target_hash: Hash = [1; 32].into();
		let target_number = 500;

		let precommit = grandpa::Precommit { target_hash: target_hash.clone(), target_number };
		let payload = super::localized_payload(
			round, set_id, &grandpa::Message::Precommit(precommit.clone())
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = key.sign(&payload[..]);
			auth_data.push((signature, public[i].0.clone()))
		}

		grandpa::CompactCommit {
			target_hash,
			target_number,
			precommits,
			auth_data,
		}
	};

	let encoded_commit = gossip::GossipMessage::<Block>::Commit(gossip::FullCommitMessage {
		round: Round(round),
		set_id: SetId(set_id),
		message: commit,
	}).encode();

	let id = network::PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network()
		.and_then(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, network::config::Roles::FULL);
			Ok((tester, id))
		})
		.and_then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) = tester.net_handle.global_communication(SetId(1), voter_set, false);

			{
				let (action, _) = tester.gossip_validator.do_validate(&id, &encoded_commit[..]);
				match action {
					gossip::Action::ProcessAndDiscard(t, _) => assert_eq!(t, global_topic),
					_ => panic!("wrong expected outcome from initial commit validation"),
				}
			}

			let commit_to_send = encoded_commit.clone();

			// asking for global communication will cause the test network
			// to send us an event asking us for a stream. use it to
			// send a message.
			let sender_id = id.clone();
			let send_message = tester.filter_network_events(move |event| match event {
				Event::MessagesFor(topic, sender) => {
					if topic != global_topic { return false }
					let _ = sender.unbounded_send(network_gossip::TopicNotification {
						message: commit_to_send.clone(),
						sender: Some(sender_id.clone()),
					});

					true
				}
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was good.
			let handle_commit = commits_in.into_future()
				.map(|(item, _)| {
					let (_, _, mut callback) = item.unwrap();
					(callback)(super::CommitProcessingOutcome::Good);
				})
				.map_err(|_| panic!("could not process commit"));

			// once the message is sent and commit is "handled" we should have
			// a repropagation event coming from the network.
			send_message.join(handle_commit).and_then(move |(tester, ())| {
				tester.filter_network_events(move |event| match event {
					Event::GossipMessage(topic, data, false) => {
						if topic == global_topic && data == encoded_commit {
							true
						} else {
							panic!("Trying to gossip something strange")
						}
					}
					_ => false,
				})
			})
				.map_err(|_| panic!("could not watch for gossip message"))
				.map(|_| ())
		});

	current_thread::block_on_all(test).unwrap();
}

#[test]
fn bad_commit_leads_to_report() {
	let private = [AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let public = make_ids(&private[..]);
	let voter_set = Arc::new(public.iter().cloned().collect::<VoterSet<AuthorityId>>());

	let round = 0;
	let set_id = 1;

	let commit = {
		let target_hash: Hash = [1; 32].into();
		let target_number = 500;

		let precommit = grandpa::Precommit { target_hash: target_hash.clone(), target_number };
		let payload = super::localized_payload(
			round, set_id, &grandpa::Message::Precommit(precommit.clone())
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = key.sign(&payload[..]);
			auth_data.push((signature, public[i].0.clone()))
		}

		grandpa::CompactCommit {
			target_hash,
			target_number,
			precommits,
			auth_data,
		}
	};

	let encoded_commit = gossip::GossipMessage::<Block>::Commit(gossip::FullCommitMessage {
		round: Round(round),
		set_id: SetId(set_id),
		message: commit,
	}).encode();

	let id = network::PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network()
		.and_then(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, network::config::Roles::FULL);
			Ok((tester, id))
		})
		.and_then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) = tester.net_handle.global_communication(SetId(1), voter_set, false);

			{
				let (action, _) = tester.gossip_validator.do_validate(&id, &encoded_commit[..]);
				match action {
					gossip::Action::ProcessAndDiscard(t, _) => assert_eq!(t, global_topic),
					_ => panic!("wrong expected outcome from initial commit validation"),
				}
			}

			let commit_to_send = encoded_commit.clone();

			// asking for global communication will cause the test network
			// to send us an event asking us for a stream. use it to
			// send a message.
			let sender_id = id.clone();
			let send_message = tester.filter_network_events(move |event| match event {
				Event::MessagesFor(topic, sender) => {
					if topic != global_topic { return false }
					let _ = sender.unbounded_send(network_gossip::TopicNotification {
						message: commit_to_send.clone(),
						sender: Some(sender_id.clone()),
					});

					true
				}
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was good.
			let handle_commit = commits_in.into_future()
				.map(|(item, _)| {
					let (_, _, mut callback) = item.unwrap();
					(callback)(super::CommitProcessingOutcome::Bad);
				})
				.map_err(|_| panic!("could not process commit"));

			// once the message is sent and commit is "handled" we should have
			// a report event coming from the network.
			send_message.join(handle_commit).and_then(move |(tester, ())| {
				tester.filter_network_events(move |event| match event {
					Event::Report(who, cost_benefit) => {
						if who == id && cost_benefit == super::cost::INVALID_COMMIT {
							true
						} else {
							panic!("reported unknown peer or unexpected cost");
						}
					}
					_ => false,
				})
			})
				.map_err(|_| panic!("could not watch for peer report"))
				.map(|_| ())
		});

	current_thread::block_on_all(test).unwrap();
}
