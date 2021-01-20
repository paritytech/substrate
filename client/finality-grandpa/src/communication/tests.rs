// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for the communication portion of the GRANDPA crate.

use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use futures::prelude::*;
use sc_network::{Event as NetworkEvent, ObservedRole, PeerId};
use sc_network_test::{Block, Hash};
use sc_network_gossip::Validator;
use std::sync::Arc;
use sp_keyring::Ed25519Keyring;
use parity_scale_codec::Encode;
use sp_runtime::traits::NumberFor;
use std::{borrow::Cow, pin::Pin, task::{Context, Poll}};
use crate::communication::GRANDPA_PROTOCOL_NAME;
use crate::environment::SharedVoterSetState;
use sp_finality_grandpa::AuthorityList;
use super::gossip::{self, GossipValidator};
use super::{VoterSet, Round, SetId};

#[derive(Debug)]
pub(crate) enum Event {
	EventStream(TracingUnboundedSender<NetworkEvent>),
	WriteNotification(sc_network::PeerId, Vec<u8>),
	Report(sc_network::PeerId, sc_network::ReputationChange),
	Announce(Hash),
}

#[derive(Clone)]
pub(crate) struct TestNetwork {
	sender: TracingUnboundedSender<Event>,
}

impl sc_network_gossip::Network<Block> for TestNetwork {
	fn event_stream(&self) -> Pin<Box<dyn Stream<Item = NetworkEvent> + Send>> {
		let (tx, rx) = tracing_unbounded("test");
		let _ = self.sender.unbounded_send(Event::EventStream(tx));
		Box::pin(rx)
	}

	fn report_peer(&self, who: sc_network::PeerId, cost_benefit: sc_network::ReputationChange) {
		let _ = self.sender.unbounded_send(Event::Report(who, cost_benefit));
	}

	fn add_set_reserved(&self, _: PeerId, _: Cow<'static, str>) {}

	fn remove_set_reserved(&self, _: PeerId, _: Cow<'static, str>) {}

	fn disconnect_peer(&self, _: PeerId, _: Cow<'static, str>) {}

	fn write_notification(&self, who: PeerId, _: Cow<'static, str>, message: Vec<u8>) {
		let _ = self.sender.unbounded_send(Event::WriteNotification(who, message));
	}

	fn announce(&self, block: Hash, _associated_data: Option<Vec<u8>>) {
		let _ = self.sender.unbounded_send(Event::Announce(block));
	}
}

impl super::Network<Block> for TestNetwork {
	fn set_sync_fork_request(
		&self,
		_peers: Vec<sc_network::PeerId>,
		_hash: Hash,
		_number: NumberFor<Block>,
	) {}
}

impl sc_network_gossip::ValidatorContext<Block> for TestNetwork {
	fn broadcast_topic(&mut self, _: Hash, _: bool) { }

	fn broadcast_message(&mut self, _: Hash, _: Vec<u8>, _: bool) {	}

	fn send_message(&mut self, who: &sc_network::PeerId, data: Vec<u8>) {
		<Self as sc_network_gossip::Network<Block>>::write_notification(
			self,
			who.clone(),
			GRANDPA_PROTOCOL_NAME.into(),
			data,
		);
	}

	fn send_topic(&mut self, _: &sc_network::PeerId, _: Hash, _: bool) { }
}

pub(crate) struct Tester {
	pub(crate) net_handle: super::NetworkBridge<Block, TestNetwork>,
	gossip_validator: Arc<GossipValidator<Block>>,
	pub(crate) events: TracingUnboundedReceiver<Event>,
}

impl Tester {
	fn filter_network_events<F>(self, mut pred: F) -> impl Future<Output = Self>
		where F: FnMut(Event) -> bool
	{
		let mut s = Some(self);
		futures::future::poll_fn(move |cx| loop {
			match Stream::poll_next(Pin::new(&mut s.as_mut().unwrap().events), cx) {
				Poll::Ready(None) => panic!("concluded early"),
				Poll::Ready(Some(item)) => if pred(item) {
					return Poll::Ready(s.take().unwrap())
				},
				Poll::Pending => return Poll::Pending,
			}
		})
	}

	pub(crate) fn trigger_gossip_validator_reputation_change(&self, p: &PeerId) {
		self.gossip_validator.validate(
			&mut crate::communication::tests::NoopContext,
			p,
			&vec![1, 2, 3],
		);
	}
}

// some random config (not really needed)
fn config() -> crate::Config {
	crate::Config {
		gossip_duration: std::time::Duration::from_millis(10),
		justification_period: 256,
		keystore: None,
		name: None,
		is_authority: true,
		observer_enabled: true,
	}
}

// dummy voter set state
fn voter_set_state() -> SharedVoterSetState<Block> {
	use crate::authorities::AuthoritySet;
	use crate::environment::VoterSetState;
	use finality_grandpa::round::State as RoundState;
	use sp_core::{crypto::Public, H256};
	use sp_finality_grandpa::AuthorityId;

	let state = RoundState::genesis((H256::zero(), 0));
	let base = state.prevote_ghost.unwrap();

	let voters = vec![(AuthorityId::from_slice(&[1; 32]), 1)];
	let voters = AuthoritySet::genesis(voters).unwrap();

	let set_state = VoterSetState::live(
		0,
		&voters,
		base,
	);

	set_state.into()
}

// needs to run in a tokio runtime.
pub(crate) fn make_test_network() -> (
	impl Future<Output = Tester>,
	TestNetwork,
) {
	let (tx, rx) = tracing_unbounded("test");
	let net = TestNetwork { sender: tx };

	#[derive(Clone)]
	struct Exit;

	impl futures::Future for Exit {
		type Output = ();

		fn poll(self: Pin<&mut Self>, _: &mut Context) -> Poll<()> {
			Poll::Pending
		}
	}

	let bridge = super::NetworkBridge::new(
		net.clone(),
		config(),
		voter_set_state(),
		None,
	);

	(
		futures::future::ready(Tester {
			gossip_validator: bridge.validator.clone(),
			net_handle: bridge,
			events: rx,
		}),
		net,
	)
}

fn make_ids(keys: &[Ed25519Keyring]) -> AuthorityList {
	keys.iter()
		.map(|key| key.clone().public().into())
		.map(|id| (id, 1))
		.collect()
}

struct NoopContext;

impl sc_network_gossip::ValidatorContext<Block> for NoopContext {
	fn broadcast_topic(&mut self, _: Hash, _: bool) { }
	fn broadcast_message(&mut self, _: Hash, _: Vec<u8>, _: bool) { }
	fn send_message(&mut self, _: &sc_network::PeerId, _: Vec<u8>) { }
	fn send_topic(&mut self, _: &sc_network::PeerId, _: Hash, _: bool) { }
}

#[test]
fn good_commit_leads_to_relay() {
	let private = [Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let public = make_ids(&private[..]);
	let voter_set = Arc::new(VoterSet::new(public.iter().cloned()).unwrap());

	let round = 1;
	let set_id = 1;

	let commit = {
		let target_hash: Hash = [1; 32].into();
		let target_number = 500;

		let precommit = finality_grandpa::Precommit { target_hash: target_hash.clone(), target_number };
		let payload = sp_finality_grandpa::localized_payload(
			round, set_id, &finality_grandpa::Message::Precommit(precommit.clone())
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = sp_finality_grandpa::AuthoritySignature::from(key.sign(&payload[..]));
			auth_data.push((signature, public[i].0.clone()))
		}

		finality_grandpa::CompactCommit {
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

	let id = sc_network::PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network().0
		.then(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, ObservedRole::Full);
			future::ready((tester, id))
		})
		.then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) = tester.net_handle.global_communication(SetId(1), voter_set, false);

			{
				let (action, ..) = tester.gossip_validator.do_validate(&id, &encoded_commit[..]);
				match action {
					gossip::Action::ProcessAndDiscard(t, _) => assert_eq!(t, global_topic),
					_ => panic!("wrong expected outcome from initial commit validation"),
				}
			}

			let commit_to_send = encoded_commit.clone();
			let network_bridge = tester.net_handle.clone();

			// asking for global communication will cause the test network
			// to send us an event asking us for a stream. use it to
			// send a message.
			let sender_id = id.clone();
			let send_message = tester.filter_network_events(move |event| match event {
				Event::EventStream(sender) => {
					// Add the sending peer and send the commit
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: sender_id.clone(),
						protocol: GRANDPA_PROTOCOL_NAME.into(),
						role: ObservedRole::Full,
					});

					let _ = sender.unbounded_send(NetworkEvent::NotificationsReceived {
						remote: sender_id.clone(),
						messages: vec![(GRANDPA_PROTOCOL_NAME.into(), commit_to_send.clone().into())],
					});

					// Add a random peer which will be the recipient of this message
					let receiver_id = sc_network::PeerId::random();
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: receiver_id.clone(),
						protocol: GRANDPA_PROTOCOL_NAME.into(),
						role: ObservedRole::Full,
					});

					// Announce its local set has being on the current set id through a neighbor
					// packet, otherwise it won't be eligible to receive the commit
					let _ = {
						let update = gossip::VersionedNeighborPacket::V1(
							gossip::NeighborPacket {
								round: Round(round),
								set_id: SetId(set_id),
								commit_finalized_height: 1,
							}
						);

						let msg = gossip::GossipMessage::<Block>::Neighbor(update);

						sender.unbounded_send(NetworkEvent::NotificationsReceived {
							remote: receiver_id,
							messages: vec![(GRANDPA_PROTOCOL_NAME.into(), msg.encode().into())],
						})
					};

					true
				}
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was good.
			let handle_commit = commits_in.into_future()
				.map(|(item, _)| {
					match item.unwrap() {
						finality_grandpa::voter::CommunicationIn::Commit(_, _, mut callback) => {
							callback.run(finality_grandpa::voter::CommitProcessingOutcome::good());
						},
						_ => panic!("commit expected"),
					}
				});

			// once the message is sent and commit is "handled" we should have
			// a repropagation event coming from the network.
			let fut = future::join(send_message, handle_commit).then(move |(tester, ())| {
				tester.filter_network_events(move |event| match event {
					Event::WriteNotification(_, data) => {
						data == encoded_commit
					}
					_ => false,
				})
			})
				.map(|_| ());

			// Poll both the future sending and handling the commit, as well as the underlying
			// NetworkBridge. Complete once the former completes.
			future::select(fut, network_bridge)
		});

	futures::executor::block_on(test);
}

#[test]
fn bad_commit_leads_to_report() {
	sp_tracing::try_init_simple();
	let private = [Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let public = make_ids(&private[..]);
	let voter_set = Arc::new(VoterSet::new(public.iter().cloned()).unwrap());

	let round = 1;
	let set_id = 1;

	let commit = {
		let target_hash: Hash = [1; 32].into();
		let target_number = 500;

		let precommit = finality_grandpa::Precommit { target_hash: target_hash.clone(), target_number };
		let payload = sp_finality_grandpa::localized_payload(
			round, set_id, &finality_grandpa::Message::Precommit(precommit.clone())
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = sp_finality_grandpa::AuthoritySignature::from(key.sign(&payload[..]));
			auth_data.push((signature, public[i].0.clone()))
		}

		finality_grandpa::CompactCommit {
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

	let id = sc_network::PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network().0
		.map(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, ObservedRole::Full);
			(tester, id)
		})
		.then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) = tester.net_handle.global_communication(SetId(1), voter_set, false);

			{
				let (action, ..) = tester.gossip_validator.do_validate(&id, &encoded_commit[..]);
				match action {
					gossip::Action::ProcessAndDiscard(t, _) => assert_eq!(t, global_topic),
					_ => panic!("wrong expected outcome from initial commit validation"),
				}
			}

			let commit_to_send = encoded_commit.clone();
			let network_bridge = tester.net_handle.clone();

			// asking for global communication will cause the test network
			// to send us an event asking us for a stream. use it to
			// send a message.
			let sender_id = id.clone();
			let send_message = tester.filter_network_events(move |event| match event {
				Event::EventStream(sender) => {
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: sender_id.clone(),
						protocol: GRANDPA_PROTOCOL_NAME.into(),
						role: ObservedRole::Full,
					});
					let _ = sender.unbounded_send(NetworkEvent::NotificationsReceived {
						remote: sender_id.clone(),
						messages: vec![(GRANDPA_PROTOCOL_NAME.into(), commit_to_send.clone().into())],
					});

					true
				}
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was bad.
			let handle_commit = commits_in.into_future()
				.map(|(item, _)| {
					match item.unwrap() {
						finality_grandpa::voter::CommunicationIn::Commit(_, _, mut callback) => {
							callback.run(finality_grandpa::voter::CommitProcessingOutcome::bad());
						},
						_ => panic!("commit expected"),
					}
				});

			// once the message is sent and commit is "handled" we should have
			// a report event coming from the network.
			let fut = future::join(send_message, handle_commit).then(move |(tester, ())| {
				tester.filter_network_events(move |event| match event {
					Event::Report(who, cost_benefit) => {
						who == id && cost_benefit == super::cost::INVALID_COMMIT
					}
					_ => false,
				})
			})
				.map(|_| ());

			// Poll both the future sending and handling the commit, as well as the underlying
			// NetworkBridge. Complete once the former completes.
			future::select(fut, network_bridge)
		});

	futures::executor::block_on(test);
}

#[test]
fn peer_with_higher_view_leads_to_catch_up_request() {
	let id = sc_network::PeerId::random();

	let (tester, mut net) = make_test_network();
	let test = tester
		.map(move |tester| {
			// register a peer with authority role.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, ObservedRole::Authority);
			(tester, id)
		})
		.then(move |(tester, id)| {
			// send neighbor message at round 10 and height 50
			let result = tester.gossip_validator.validate(
				&mut net,
				&id,
				&gossip::GossipMessage::<Block>::from(gossip::NeighborPacket {
					set_id: SetId(0),
					round: Round(10),
					commit_finalized_height: 50,
				}).encode(),
			);

			// neighbor packets are always discard
			match result {
				sc_network_gossip::ValidationResult::Discard => {},
				_ => panic!("wrong expected outcome from neighbor validation"),
			}

			// a catch up request should be sent to the peer for round - 1
			tester.filter_network_events(move |event| match event {
				Event::WriteNotification(peer, message) => {
					assert_eq!(
						peer,
						id,
					);

					assert_eq!(
						message,
						gossip::GossipMessage::<Block>::CatchUpRequest(
							gossip::CatchUpRequestMessage {
								set_id: SetId(0),
								round: Round(9),
							}
						).encode(),
					);

					true
				},
				_ => false,
			})
				.map(|_| ())
		});

	futures::executor::block_on(test);
}
