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

//! Tests for the communication portion of the GRANDPA crate.

use super::{
	gossip::{self, GossipValidator},
	Round, SetId, VoterSet,
};
use crate::{communication::grandpa_protocol_name, environment::SharedVoterSetState};
use futures::prelude::*;
use parity_scale_codec::Encode;
use sc_network::{
	config::{MultiaddrWithPeerId, Role},
	event::Event as NetworkEvent,
	types::ProtocolName,
	Multiaddr, NetworkBlock, NetworkEventStream, NetworkNotification, NetworkPeers,
	NetworkSyncForkRequest, NotificationSenderError, NotificationSenderT as NotificationSender,
	PeerId, ReputationChange,
};
use sc_network_common::{
	role::ObservedRole,
	sync::{SyncEvent as SyncStreamEvent, SyncEventStream},
};
use sc_network_gossip::Validator;
use sc_network_test::{Block, Hash};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_consensus_grandpa::AuthorityList;
use sp_keyring::Ed25519Keyring;
use sp_runtime::traits::NumberFor;
use std::{
	collections::HashSet,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
};

#[derive(Debug)]
pub(crate) enum Event {
	EventStream(TracingUnboundedSender<NetworkEvent>),
	WriteNotification(PeerId, Vec<u8>),
	Report(PeerId, ReputationChange),
	Announce(Hash),
}

#[derive(Clone)]
pub(crate) struct TestNetwork {
	sender: TracingUnboundedSender<Event>,
}

impl NetworkPeers for TestNetwork {
	fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
		unimplemented!();
	}

	fn set_authorized_only(&self, _reserved_only: bool) {
		unimplemented!();
	}

	fn add_known_address(&self, _peer_id: PeerId, _addr: Multiaddr) {
		unimplemented!();
	}

	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		let _ = self.sender.unbounded_send(Event::Report(who, cost_benefit));
	}

	fn disconnect_peer(&self, _who: PeerId, _protocol: ProtocolName) {}

	fn accept_unreserved_peers(&self) {
		unimplemented!();
	}

	fn deny_unreserved_peers(&self) {
		unimplemented!();
	}

	fn add_reserved_peer(&self, _peer: MultiaddrWithPeerId) -> Result<(), String> {
		unimplemented!();
	}

	fn remove_reserved_peer(&self, _peer_id: PeerId) {
		unimplemented!();
	}

	fn set_reserved_peers(
		&self,
		_protocol: ProtocolName,
		_peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		unimplemented!();
	}

	fn add_peers_to_reserved_set(
		&self,
		_protocol: ProtocolName,
		_peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		unimplemented!();
	}

	fn remove_peers_from_reserved_set(
		&self,
		_protocol: ProtocolName,
		_peers: Vec<PeerId>,
	) -> Result<(), String> {
		unimplemented!();
	}

	fn sync_num_connected(&self) -> usize {
		unimplemented!();
	}
}

impl NetworkEventStream for TestNetwork {
	fn event_stream(
		&self,
		_name: &'static str,
	) -> Pin<Box<dyn Stream<Item = NetworkEvent> + Send>> {
		let (tx, rx) = tracing_unbounded("test", 100_000);
		let _ = self.sender.unbounded_send(Event::EventStream(tx));
		Box::pin(rx)
	}
}

impl NetworkNotification for TestNetwork {
	fn write_notification(&self, target: PeerId, _protocol: ProtocolName, message: Vec<u8>) {
		let _ = self.sender.unbounded_send(Event::WriteNotification(target, message));
	}

	fn notification_sender(
		&self,
		_target: PeerId,
		_protocol: ProtocolName,
	) -> Result<Box<dyn NotificationSender>, NotificationSenderError> {
		unimplemented!();
	}

	fn set_notification_handshake(&self, _protocol: ProtocolName, _handshake: Vec<u8>) {
		unimplemented!();
	}
}

impl NetworkBlock<Hash, NumberFor<Block>> for TestNetwork {
	fn announce_block(&self, hash: Hash, _data: Option<Vec<u8>>) {
		let _ = self.sender.unbounded_send(Event::Announce(hash));
	}

	fn new_best_block_imported(&self, _hash: Hash, _number: NumberFor<Block>) {
		unimplemented!();
	}
}

impl NetworkSyncForkRequest<Hash, NumberFor<Block>> for TestNetwork {
	fn set_sync_fork_request(&self, _peers: Vec<PeerId>, _hash: Hash, _number: NumberFor<Block>) {}
}

impl sc_network_gossip::ValidatorContext<Block> for TestNetwork {
	fn broadcast_topic(&mut self, _: Hash, _: bool) {}

	fn broadcast_message(&mut self, _: Hash, _: Vec<u8>, _: bool) {}

	fn send_message(&mut self, who: &PeerId, data: Vec<u8>) {
		<Self as NetworkNotification>::write_notification(
			self,
			*who,
			grandpa_protocol_name::NAME.into(),
			data,
		);
	}

	fn send_topic(&mut self, _: &PeerId, _: Hash, _: bool) {}
}

#[derive(Clone)]
pub(crate) struct TestSync;

impl SyncEventStream for TestSync {
	fn event_stream(
		&self,
		_name: &'static str,
	) -> Pin<Box<dyn Stream<Item = SyncStreamEvent> + Send>> {
		Box::pin(futures::stream::pending())
	}
}

impl NetworkBlock<Hash, NumberFor<Block>> for TestSync {
	fn announce_block(&self, _hash: Hash, _data: Option<Vec<u8>>) {
		unimplemented!();
	}

	fn new_best_block_imported(&self, _hash: Hash, _number: NumberFor<Block>) {
		unimplemented!();
	}
}

impl NetworkSyncForkRequest<Hash, NumberFor<Block>> for TestSync {
	fn set_sync_fork_request(&self, _peers: Vec<PeerId>, _hash: Hash, _number: NumberFor<Block>) {}
}

pub(crate) struct Tester {
	pub(crate) net_handle: super::NetworkBridge<Block, TestNetwork, TestSync>,
	gossip_validator: Arc<GossipValidator<Block>>,
	pub(crate) events: TracingUnboundedReceiver<Event>,
}

impl Tester {
	fn filter_network_events<F>(self, mut pred: F) -> impl Future<Output = Self>
	where
		F: FnMut(Event) -> bool,
	{
		let mut s = Some(self);
		futures::future::poll_fn(move |cx| loop {
			match Stream::poll_next(Pin::new(&mut s.as_mut().unwrap().events), cx) {
				Poll::Ready(None) => panic!("concluded early"),
				Poll::Ready(Some(item)) =>
					if pred(item) {
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
		justification_generation_period: 256,
		keystore: None,
		name: None,
		local_role: Role::Authority,
		observer_enabled: true,
		telemetry: None,
		protocol_name: grandpa_protocol_name::NAME.into(),
	}
}

// dummy voter set state
fn voter_set_state() -> SharedVoterSetState<Block> {
	use crate::{authorities::AuthoritySet, environment::VoterSetState};
	use finality_grandpa::round::State as RoundState;
	use sp_consensus_grandpa::AuthorityId;
	use sp_core::{crypto::ByteArray, H256};

	let state = RoundState::genesis((H256::zero(), 0));
	let base = state.prevote_ghost.unwrap();

	let voters = vec![(AuthorityId::from_slice(&[1; 32]).unwrap(), 1)];
	let voters = AuthoritySet::genesis(voters).unwrap();

	let set_state = VoterSetState::live(0, &voters, base);

	set_state.into()
}

// needs to run in a tokio runtime.
pub(crate) fn make_test_network() -> (impl Future<Output = Tester>, TestNetwork) {
	let (tx, rx) = tracing_unbounded("test", 100_000);
	let net = TestNetwork { sender: tx };
	let sync = TestSync {};

	#[derive(Clone)]
	struct Exit;

	impl futures::Future for Exit {
		type Output = ();

		fn poll(self: Pin<&mut Self>, _: &mut Context) -> Poll<()> {
			Poll::Pending
		}
	}

	let bridge =
		super::NetworkBridge::new(net.clone(), sync, config(), voter_set_state(), None, None);

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
	keys.iter().map(|&key| key.public().into()).map(|id| (id, 1)).collect()
}

struct NoopContext;

impl sc_network_gossip::ValidatorContext<Block> for NoopContext {
	fn broadcast_topic(&mut self, _: Hash, _: bool) {}
	fn broadcast_message(&mut self, _: Hash, _: Vec<u8>, _: bool) {}
	fn send_message(&mut self, _: &PeerId, _: Vec<u8>) {}
	fn send_topic(&mut self, _: &PeerId, _: Hash, _: bool) {}
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

		let precommit = finality_grandpa::Precommit { target_hash, target_number };
		let payload = sp_consensus_grandpa::localized_payload(
			round,
			set_id,
			&finality_grandpa::Message::Precommit(precommit.clone()),
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = sp_consensus_grandpa::AuthoritySignature::from(key.sign(&payload[..]));
			auth_data.push((signature, public[i].0.clone()))
		}

		finality_grandpa::CompactCommit { target_hash, target_number, precommits, auth_data }
	};

	let encoded_commit = gossip::GossipMessage::<Block>::Commit(gossip::FullCommitMessage {
		round: Round(round),
		set_id: SetId(set_id),
		message: commit,
	})
	.encode();

	let id = PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network()
		.0
		.then(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, ObservedRole::Full);
			future::ready((tester, id))
		})
		.then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) =
				tester.net_handle.global_communication(SetId(1), voter_set, false);

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
			let sender_id = id;
			let send_message = tester.filter_network_events(move |event| match event {
				Event::EventStream(sender) => {
					// Add the sending peer and send the commit
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: sender_id,
						protocol: grandpa_protocol_name::NAME.into(),
						negotiated_fallback: None,
						role: ObservedRole::Full,
						received_handshake: vec![],
					});

					let _ = sender.unbounded_send(NetworkEvent::NotificationsReceived {
						remote: sender_id,
						messages: vec![(
							grandpa_protocol_name::NAME.into(),
							commit_to_send.clone().into(),
						)],
					});

					// Add a random peer which will be the recipient of this message
					let receiver_id = PeerId::random();
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: receiver_id,
						protocol: grandpa_protocol_name::NAME.into(),
						negotiated_fallback: None,
						role: ObservedRole::Full,
						received_handshake: vec![],
					});

					// Announce its local set has being on the current set id through a neighbor
					// packet, otherwise it won't be eligible to receive the commit
					let _ = {
						let update = gossip::VersionedNeighborPacket::V1(gossip::NeighborPacket {
							round: Round(round),
							set_id: SetId(set_id),
							commit_finalized_height: 1,
						});

						let msg = gossip::GossipMessage::<Block>::Neighbor(update);

						sender.unbounded_send(NetworkEvent::NotificationsReceived {
							remote: receiver_id,
							messages: vec![(
								grandpa_protocol_name::NAME.into(),
								msg.encode().into(),
							)],
						})
					};

					true
				},
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was good.
			let handle_commit = commits_in.into_future().map(|(item, _)| match item.unwrap() {
				finality_grandpa::voter::CommunicationIn::Commit(_, _, mut callback) => {
					callback.run(finality_grandpa::voter::CommitProcessingOutcome::good());
				},
				_ => panic!("commit expected"),
			});

			// once the message is sent and commit is "handled" we should have
			// a repropagation event coming from the network.
			let fut = future::join(send_message, handle_commit)
				.then(move |(tester, ())| {
					tester.filter_network_events(move |event| match event {
						Event::WriteNotification(_, data) => data == encoded_commit,
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

		let precommit = finality_grandpa::Precommit { target_hash, target_number };
		let payload = sp_consensus_grandpa::localized_payload(
			round,
			set_id,
			&finality_grandpa::Message::Precommit(precommit.clone()),
		);

		let mut precommits = Vec::new();
		let mut auth_data = Vec::new();

		for (i, key) in private.iter().enumerate() {
			precommits.push(precommit.clone());

			let signature = sp_consensus_grandpa::AuthoritySignature::from(key.sign(&payload[..]));
			auth_data.push((signature, public[i].0.clone()))
		}

		finality_grandpa::CompactCommit { target_hash, target_number, precommits, auth_data }
	};

	let encoded_commit = gossip::GossipMessage::<Block>::Commit(gossip::FullCommitMessage {
		round: Round(round),
		set_id: SetId(set_id),
		message: commit,
	})
	.encode();

	let id = PeerId::random();
	let global_topic = super::global_topic::<Block>(set_id);

	let test = make_test_network()
		.0
		.map(move |tester| {
			// register a peer.
			tester.gossip_validator.new_peer(&mut NoopContext, &id, ObservedRole::Full);
			(tester, id)
		})
		.then(move |(tester, id)| {
			// start round, dispatch commit, and wait for broadcast.
			let (commits_in, _) =
				tester.net_handle.global_communication(SetId(1), voter_set, false);

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
			let sender_id = id;
			let send_message = tester.filter_network_events(move |event| match event {
				Event::EventStream(sender) => {
					let _ = sender.unbounded_send(NetworkEvent::NotificationStreamOpened {
						remote: sender_id,
						protocol: grandpa_protocol_name::NAME.into(),
						negotiated_fallback: None,
						role: ObservedRole::Full,
						received_handshake: vec![],
					});
					let _ = sender.unbounded_send(NetworkEvent::NotificationsReceived {
						remote: sender_id,
						messages: vec![(
							grandpa_protocol_name::NAME.into(),
							commit_to_send.clone().into(),
						)],
					});

					true
				},
				_ => false,
			});

			// when the commit comes in, we'll tell the callback it was bad.
			let handle_commit = commits_in.into_future().map(|(item, _)| match item.unwrap() {
				finality_grandpa::voter::CommunicationIn::Commit(_, _, mut callback) => {
					callback.run(finality_grandpa::voter::CommitProcessingOutcome::bad());
				},
				_ => panic!("commit expected"),
			});

			// once the message is sent and commit is "handled" we should have
			// a report event coming from the network.
			let fut = future::join(send_message, handle_commit)
				.then(move |(tester, ())| {
					tester.filter_network_events(move |event| match event {
						Event::Report(who, cost_benefit) =>
							who == id && cost_benefit == super::cost::INVALID_COMMIT,
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
	let id = PeerId::random();

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
				})
				.encode(),
			);

			// neighbor packets are always discard
			match result {
				sc_network_gossip::ValidationResult::Discard => {},
				_ => panic!("wrong expected outcome from neighbor validation"),
			}

			// a catch up request should be sent to the peer for round - 1
			tester
				.filter_network_events(move |event| match event {
					Event::WriteNotification(peer, message) => {
						assert_eq!(peer, id);

						assert_eq!(
							message,
							gossip::GossipMessage::<Block>::CatchUpRequest(
								gossip::CatchUpRequestMessage { set_id: SetId(0), round: Round(9) }
							)
							.encode(),
						);

						true
					},
					_ => false,
				})
				.map(|_| ())
		});

	futures::executor::block_on(test);
}

fn local_chain_spec() -> Box<dyn sc_chain_spec::ChainSpec> {
	use sc_chain_spec::{ChainSpec, GenericChainSpec};
	use serde::{Deserialize, Serialize};
	use sp_runtime::{BuildStorage, Storage};

	#[derive(Debug, Serialize, Deserialize)]
	struct Genesis(std::collections::BTreeMap<String, String>);
	impl BuildStorage for Genesis {
		fn assimilate_storage(&self, storage: &mut Storage) -> Result<(), String> {
			storage.top.extend(
				self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes())),
			);
			Ok(())
		}
	}
	let chain_spec = GenericChainSpec::<Genesis>::from_json_bytes(
		&include_bytes!("../../../../chain-spec/res/chain_spec.json")[..],
	)
	.unwrap();
	chain_spec.cloned_box()
}

#[test]
fn grandpa_protocol_name() {
	let chain_spec = local_chain_spec();

	// Create protocol name using random genesis hash.
	let genesis_hash = sp_core::H256::random();
	let expected = format!("/{}/grandpa/1", array_bytes::bytes2hex("", genesis_hash));
	let proto_name = grandpa_protocol_name::standard_name(&genesis_hash, &chain_spec);
	assert_eq!(proto_name.to_string(), expected);

	// Create protocol name using hardcoded genesis hash. Verify exact representation.
	let genesis_hash = [
		53, 79, 112, 97, 119, 217, 39, 202, 147, 138, 225, 38, 88, 182, 215, 185, 110, 88, 8, 53,
		125, 210, 158, 151, 50, 113, 102, 59, 245, 199, 221, 240,
	];
	let expected =
		"/354f706177d927ca938ae12658b6d7b96e5808357dd29e973271663bf5c7ddf0/grandpa/1".to_string();
	let proto_name = grandpa_protocol_name::standard_name(&genesis_hash, &chain_spec);
	assert_eq!(proto_name.to_string(), expected);
}
