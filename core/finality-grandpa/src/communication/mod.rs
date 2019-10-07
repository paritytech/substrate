// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Communication streams for the polite-grandpa networking protocol.
//!
//! GRANDPA nodes communicate over a gossip network, where messages are not sent to
//! peers until they have reached a given round.
//!
//! Rather than expressing protocol rules,
//! polite-grandpa just carries a notion of impoliteness. Nodes which pass some arbitrary
//! threshold of impoliteness are removed. Messages are either costly, or beneficial.
//!
//! For instance, it is _impolite_ to send the same message more than once.
//! In the future, there will be a fallback for allowing sending the same message
//! under certain conditions that are used to un-stick the protocol.

use std::sync::Arc;

use futures::prelude::*;
use futures::sync::{oneshot, mpsc};
use grandpa::Message::{Prevote, Precommit, PrimaryPropose};
use grandpa::{voter, voter_set::VoterSet};
use log::{debug, trace};
use network::{consensus_gossip as network_gossip, NetworkService};
use network_gossip::ConsensusMessage;
use codec::{Encode, Decode};
use primitives::Pair;
use sr_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT};
use substrate_telemetry::{telemetry, CONSENSUS_DEBUG, CONSENSUS_INFO};
use tokio_executor::Executor;

use crate::{
	CatchUp, Commit, CommunicationIn, CommunicationOut, CompactCommit, Error,
	Message, SignedMessage,
};
use crate::environment::HasVoted;
use gossip::{
	GossipMessage, FullCatchUpMessage, FullCommitMessage, VoteOrPrecommitMessage, GossipValidator
};
use fg_primitives::{
	AuthorityPair, AuthorityId, AuthoritySignature, SetId as SetIdNumber, RoundNumber,
};

pub mod gossip;
mod periodic;

#[cfg(test)]
mod tests;

pub use fg_primitives::GRANDPA_ENGINE_ID;

// cost scalars for reporting peers.
mod cost {
	pub(super) const PAST_REJECTION: i32 = -50;
	pub(super) const BAD_SIGNATURE: i32 = -100;
	pub(super) const MALFORMED_CATCH_UP: i32 = -1000;
	pub(super) const MALFORMED_COMMIT: i32 = -1000;
	pub(super) const FUTURE_MESSAGE: i32 = -500;
	pub(super) const UNKNOWN_VOTER: i32 = -150;

	pub(super) const INVALID_VIEW_CHANGE: i32 = -500;
	pub(super) const PER_UNDECODABLE_BYTE: i32 = -5;
	pub(super) const PER_SIGNATURE_CHECKED: i32 = -25;
	pub(super) const PER_BLOCK_LOADED: i32 = -10;
	pub(super) const INVALID_CATCH_UP: i32 = -5000;
	pub(super) const INVALID_COMMIT: i32 = -5000;
	pub(super) const OUT_OF_SCOPE_MESSAGE: i32 = -500;
	pub(super) const CATCH_UP_REQUEST_TIMEOUT: i32 = -200;

	// cost of answering a catch up request
	pub(super) const CATCH_UP_REPLY: i32 = -200;
	pub(super) const HONEST_OUT_OF_SCOPE_CATCH_UP: i32 = -200;
}

// benefit scalars for reporting peers.
mod benefit {
	pub(super) const NEIGHBOR_MESSAGE: i32 = 100;
	pub(super) const ROUND_MESSAGE: i32 = 100;
	pub(super) const BASIC_VALIDATED_CATCH_UP: i32 = 200;
	pub(super) const BASIC_VALIDATED_COMMIT: i32 = 100;
	pub(super) const PER_EQUIVOCATION: i32 = 10;
}

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
pub trait Network<Block: BlockT>: Clone + Send + 'static {
	/// A stream of input messages for a topic.
	type In: Stream<Item=network_gossip::TopicNotification,Error=()>;

	/// Get a stream of messages for a specific gossip topic.
	fn messages_for(&self, topic: Block::Hash) -> Self::In;

	/// Register a gossip validator.
	fn register_validator(&self, validator: Arc<dyn network_gossip::Validator<Block>>);

	/// Gossip a message out to all connected peers.
	///
	/// Force causes it to be sent to all peers, even if they've seen it already.
	/// Only should be used in case of consensus stall.
	fn gossip_message(&self, topic: Block::Hash, data: Vec<u8>, force: bool);

	/// Register a message with the gossip service, it isn't broadcast right
	/// away to any peers, but may be sent to new peers joining or when asked to
	/// broadcast the topic. Useful to register previous messages on node
	/// startup.
	fn register_gossip_message(&self, topic: Block::Hash, data: Vec<u8>);

	/// Send a message to a bunch of specific peers, even if they've seen it already.
	fn send_message(&self, who: Vec<network::PeerId>, data: Vec<u8>);

	/// Report a peer's cost or benefit after some action.
	fn report(&self, who: network::PeerId, cost_benefit: i32);

	/// Inform peers that a block with given hash should be downloaded.
	fn announce(&self, block: Block::Hash, associated_data: Vec<u8>);
}

/// Create a unique topic for a round and set-id combo.
pub(crate) fn round_topic<B: BlockT>(round: RoundNumber, set_id: SetIdNumber) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-{}", set_id, round).as_bytes())
}

/// Create a unique topic for global messages on a set ID.
pub(crate) fn global_topic<B: BlockT>(set_id: SetIdNumber) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-GLOBAL", set_id).as_bytes())
}

impl<B, S, H> Network<B> for Arc<NetworkService<B, S, H>> where
	B: BlockT,
	S: network::specialization::NetworkSpecialization<B>,
	H: network::ExHashT,
{
	type In = NetworkStream;

	fn messages_for(&self, topic: B::Hash) -> Self::In {
		let (tx, rx) = oneshot::channel();
		self.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(GRANDPA_ENGINE_ID, topic);
			let _ = tx.send(inner_rx);
		});
		NetworkStream { outer: rx, inner: None }
	}

	fn register_validator(&self, validator: Arc<dyn network_gossip::Validator<B>>) {
		self.with_gossip(
			move |gossip, context| gossip.register_validator(context, GRANDPA_ENGINE_ID, validator)
		)
	}

	fn gossip_message(&self, topic: B::Hash, data: Vec<u8>, force: bool) {
		let msg = ConsensusMessage {
			engine_id: GRANDPA_ENGINE_ID,
			data,
		};

		self.with_gossip(
			move |gossip, ctx| gossip.multicast(ctx, topic, msg, force)
		)
	}

	fn register_gossip_message(&self, topic: B::Hash, data: Vec<u8>) {
		let msg = ConsensusMessage {
			engine_id: GRANDPA_ENGINE_ID,
			data,
		};

		self.with_gossip(move |gossip, _| gossip.register_message(topic, msg))
	}

	fn send_message(&self, who: Vec<network::PeerId>, data: Vec<u8>) {
		let msg = ConsensusMessage {
			engine_id: GRANDPA_ENGINE_ID,
			data,
		};

		self.with_gossip(move |gossip, ctx| for who in &who {
			gossip.send_message(ctx, who, msg.clone())
		})
	}

	fn report(&self, who: network::PeerId, cost_benefit: i32) {
		self.report_peer(who, cost_benefit)
	}

	fn announce(&self, block: B::Hash, associated_data: Vec<u8>) {
		self.announce_block(block, associated_data)
	}
}

/// A stream used by NetworkBridge in its implementation of Network.
pub struct NetworkStream {
	inner: Option<mpsc::UnboundedReceiver<network_gossip::TopicNotification>>,
	outer: oneshot::Receiver<mpsc::UnboundedReceiver<network_gossip::TopicNotification>>
}

impl Stream for NetworkStream {
	type Item = network_gossip::TopicNotification;
	type Error = ();

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		if let Some(ref mut inner) = self.inner {
			return inner.poll();
		}
		match self.outer.poll() {
			Ok(futures::Async::Ready(mut inner)) => {
				let poll_result = inner.poll();
				self.inner = Some(inner);
				poll_result
			},
			Ok(futures::Async::NotReady) => Ok(futures::Async::NotReady),
			Err(_) => Err(())
		}
	}
}

/// Bridge between the underlying network service, gossiping consensus messages and Grandpa
pub(crate) struct NetworkBridge<B: BlockT, N: Network<B>> {
	service: N,
	validator: Arc<GossipValidator<B>>,
	neighbor_sender: periodic::NeighborPacketSender<B>,
	announce_sender: periodic::BlockAnnounceSender<B>,
}

impl<B: BlockT, N: Network<B>> NetworkBridge<B, N> {
	/// Create a new NetworkBridge to the given NetworkService. Returns the service
	/// handle and a future that must be polled to completion to finish startup.
	/// On creation it will register previous rounds' votes with the gossip
	/// service taken from the VoterSetState.
	pub(crate) fn new(
		service: N,
		config: crate::Config,
		set_state: crate::environment::SharedVoterSetState<B>,
		on_exit: impl Future<Item=(),Error=()> + Clone + Send + 'static,
		catch_up_enabled: bool,
	) -> (
		Self,
		impl futures::Future<Item = (), Error = ()> + Send + 'static,
	) {

		let (validator, report_stream) = GossipValidator::new(
			config,
			set_state.clone(),
			catch_up_enabled,
		);

		let validator = Arc::new(validator);
		service.register_validator(validator.clone());

		{
			// register all previous votes with the gossip service so that they're
			// available to peers potentially stuck on a previous round.
			let completed = set_state.read().completed_rounds();
			let (set_id, voters) = completed.set_info();
			validator.note_set(SetId(set_id), voters.to_vec(), |_, _| {});
			for round in completed.iter() {
				let topic = round_topic::<B>(round.number, set_id);

				// we need to note the round with the gossip validator otherwise
				// messages will be ignored.
				validator.note_round(Round(round.number), |_, _| {});

				for signed in round.votes.iter() {
					let message = gossip::GossipMessage::VoteOrPrecommit(
						gossip::VoteOrPrecommitMessage::<B> {
							message: signed.clone(),
							round: Round(round.number),
							set_id: SetId(set_id),
						}
					);

					service.register_gossip_message(
						topic,
						message.encode(),
					);
				}

				trace!(target: "afg",
					"Registered {} messages for topic {:?} (round: {}, set_id: {})",
					round.votes.len(),
					topic,
					round.number,
					set_id,
				);
			}
		}

		let (rebroadcast_job, neighbor_sender) = periodic::neighbor_packet_worker(service.clone());
		let (announce_job, announce_sender) = periodic::block_announce_worker(service.clone());
		let reporting_job = report_stream.consume(service.clone());

		let bridge = NetworkBridge { service, validator, neighbor_sender, announce_sender };

		let startup_work = futures::future::lazy(move || {
			// lazily spawn these jobs onto their own tasks. the lazy future has access
			// to tokio globals, which aren't available outside.
			let mut executor = tokio_executor::DefaultExecutor::current();
			executor.spawn(Box::new(rebroadcast_job.select(on_exit.clone()).then(|_| Ok(()))))
				.expect("failed to spawn grandpa rebroadcast job task");
			executor.spawn(Box::new(announce_job.select(on_exit.clone()).then(|_| Ok(()))))
				.expect("failed to spawn grandpa block announce job task");
			executor.spawn(Box::new(reporting_job.select(on_exit.clone()).then(|_| Ok(()))))
				.expect("failed to spawn grandpa reporting job task");
			Ok(())
		});

		(bridge, startup_work)
	}

	/// Note the beginning of a new round to the `GossipValidator`.
	pub(crate) fn note_round(
		&self,
		round: Round,
		set_id: SetId,
		voters: &VoterSet<AuthorityId>,
	) {
		// is a no-op if currently in that set.
		self.validator.note_set(
			set_id,
			voters.voters().iter().map(|(v, _)| v.clone()).collect(),
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);

		self.validator.note_round(
			round,
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);
	}

	/// Get the round messages for a round in the current set ID. These are signature-checked.
	pub(crate) fn round_communication(
		&self,
		round: Round,
		set_id: SetId,
		voters: Arc<VoterSet<AuthorityId>>,
		local_key: Option<AuthorityPair>,
		has_voted: HasVoted<B>,
	) -> (
		impl Stream<Item=SignedMessage<B>,Error=Error>,
		impl Sink<SinkItem=Message<B>,SinkError=Error>,
	) {
		self.note_round(
			round,
			set_id,
			&*voters,
		);

		let locals = local_key.and_then(|pair| {
			let id = pair.public();
			if voters.contains_key(&id) {
				Some((pair, id))
			} else {
				None
			}
		});

		let topic = round_topic::<B>(round.0, set_id.0);
		let incoming = self.service.messages_for(topic)
			.filter_map(|notification| {
				let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);
				if let Err(ref e) = decoded {
					debug!(target: "afg", "Skipping malformed message {:?}: {}", notification, e);
				}
				decoded.ok()
			})
			.and_then(move |msg| {
				match msg {
					GossipMessage::VoteOrPrecommit(msg) => {
						// check signature.
						if !voters.contains_key(&msg.message.id) {
							debug!(target: "afg", "Skipping message from unknown voter {}", msg.message.id);
							return Ok(None);
						}

						match &msg.message.message {
							PrimaryPropose(propose) => {
								telemetry!(CONSENSUS_INFO; "afg.received_propose";
									"voter" => ?format!("{}", msg.message.id),
									"target_number" => ?propose.target_number,
									"target_hash" => ?propose.target_hash,
								);
							},
							Prevote(prevote) => {
								telemetry!(CONSENSUS_INFO; "afg.received_prevote";
									"voter" => ?format!("{}", msg.message.id),
									"target_number" => ?prevote.target_number,
									"target_hash" => ?prevote.target_hash,
								);
							},
							Precommit(precommit) => {
								telemetry!(CONSENSUS_INFO; "afg.received_precommit";
									"voter" => ?format!("{}", msg.message.id),
									"target_number" => ?precommit.target_number,
									"target_hash" => ?precommit.target_hash,
								);
							},
						};

						Ok(Some(msg.message))
					}
					_ => {
						debug!(target: "afg", "Skipping unknown message type");
						return Ok(None);
					}
				}
			})
			.filter_map(|x| x)
			.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")));

		let (tx, out_rx) = mpsc::unbounded();
		let outgoing = OutgoingMessages::<B, N> {
			round: round.0,
			set_id: set_id.0,
			network: self.service.clone(),
			locals,
			sender: tx,
			announce_sender: self.announce_sender.clone(),
			has_voted,
		};

		let out_rx = out_rx.map_err(move |()| Error::Network(
			format!("Failed to receive on unbounded receiver for round {}", round.0)
		));

		let incoming = incoming.select(out_rx);

		(incoming, outgoing)
	}

	/// Set up the global communication streams.
	pub(crate) fn global_communication(
		&self,
		set_id: SetId,
		voters: Arc<VoterSet<AuthorityId>>,
		is_voter: bool,
	) -> (
		impl Stream<Item = CommunicationIn<B>, Error = Error>,
		impl Sink<SinkItem = CommunicationOut<B>, SinkError = Error>,
	) {
		self.validator.note_set(
			set_id,
			voters.voters().iter().map(|(v, _)| v.clone()).collect(),
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);

		let service = self.service.clone();
		let topic = global_topic::<B>(set_id.0);
		let incoming = incoming_global(
			service,
			topic,
			voters,
			self.validator.clone(),
			self.neighbor_sender.clone(),
		);

		let outgoing = CommitsOut::<B, N>::new(
			self.service.clone(),
			set_id.0,
			is_voter,
			self.validator.clone(),
			self.neighbor_sender.clone(),
		);

		let outgoing = outgoing.with(|out| {
			let voter::CommunicationOut::Commit(round, commit) = out;
			Ok((round, commit))
		});

		(incoming, outgoing)
	}
}

fn incoming_global<B: BlockT, N: Network<B>>(
	mut service: N,
	topic: B::Hash,
	voters: Arc<VoterSet<AuthorityId>>,
	gossip_validator: Arc<GossipValidator<B>>,
	neighbor_sender: periodic::NeighborPacketSender<B>,
) -> impl Stream<Item = CommunicationIn<B>, Error = Error> {
	let process_commit = move |
		msg: FullCommitMessage<B>,
		mut notification: network_gossip::TopicNotification,
		service: &mut N,
		gossip_validator: &Arc<GossipValidator<B>>,
		voters: &VoterSet<AuthorityId>,
	| {
		let precommits_signed_by: Vec<String> =
			msg.message.auth_data.iter().map(move |(_, a)| {
				format!("{}", a)
			}).collect();

		telemetry!(CONSENSUS_INFO; "afg.received_commit";
			"contains_precommits_signed_by" => ?precommits_signed_by,
			"target_number" => ?msg.message.target_number.clone(),
			"target_hash" => ?msg.message.target_hash.clone(),
		);

		if let Err(cost) = check_compact_commit::<B>(
			&msg.message,
			voters,
			msg.round,
			msg.set_id,
		) {
			if let Some(who) = notification.sender {
				service.report(who, cost);
			}

			return None;
		}

		let round = msg.round.0;
		let commit = msg.message;
		let finalized_number = commit.target_number;
		let gossip_validator = gossip_validator.clone();
		let service = service.clone();
		let neighbor_sender = neighbor_sender.clone();
		let cb = move |outcome| match outcome {
			voter::CommitProcessingOutcome::Good(_) => {
				// if it checks out, gossip it. not accounting for
				// any discrepancy between the actual ghost and the claimed
				// finalized number.
				gossip_validator.note_commit_finalized(
					finalized_number,
					|to, neighbor| neighbor_sender.send(to, neighbor),
				);

				service.gossip_message(topic, notification.message.clone(), false);
			}
			voter::CommitProcessingOutcome::Bad(_) => {
				// report peer and do not gossip.
				if let Some(who) = notification.sender.take() {
					service.report(who, cost::INVALID_COMMIT);
				}
			}
		};

		let cb = voter::Callback::Work(Box::new(cb));

		Some(voter::CommunicationIn::Commit(round, commit, cb))
	};

	let process_catch_up = move |
		msg: FullCatchUpMessage<B>,
		mut notification: network_gossip::TopicNotification,
		service: &mut N,
		gossip_validator: &Arc<GossipValidator<B>>,
		voters: &VoterSet<AuthorityId>,
	| {
		let gossip_validator = gossip_validator.clone();
		let service = service.clone();

		if let Err(cost) = check_catch_up::<B>(
			&msg.message,
			voters,
			msg.set_id,
		) {
			if let Some(who) = notification.sender {
				service.report(who, cost);
			}

			return None;
		}

		let cb = move |outcome| {
			if let voter::CatchUpProcessingOutcome::Bad(_) = outcome {
				// report peer
				if let Some(who) = notification.sender.take() {
					service.report(who, cost::INVALID_CATCH_UP);
				}
			}

			gossip_validator.note_catch_up_message_processed();
		};

		let cb = voter::Callback::Work(Box::new(cb));

		Some(voter::CommunicationIn::CatchUp(msg.message, cb))
	};

	service.messages_for(topic)
		.filter_map(|notification| {
			// this could be optimized by decoding piecewise.
			let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);
			if let Err(ref e) = decoded {
				trace!(target: "afg", "Skipping malformed commit message {:?}: {}", notification, e);
			}
			decoded.map(move |d| (notification, d)).ok()
		})
		.filter_map(move |(notification, msg)| {
			match msg {
				GossipMessage::Commit(msg) =>
					process_commit(msg, notification, &mut service, &gossip_validator, &*voters),
				GossipMessage::CatchUp(msg) =>
					process_catch_up(msg, notification, &mut service, &gossip_validator, &*voters),
				_ => {
					debug!(target: "afg", "Skipping unknown message type");
					return None;
				}
			}
		})
		.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")))
}

impl<B: BlockT, N: Network<B>> Clone for NetworkBridge<B, N> {
	fn clone(&self) -> Self {
		NetworkBridge {
			service: self.service.clone(),
			validator: Arc::clone(&self.validator),
			neighbor_sender: self.neighbor_sender.clone(),
			announce_sender: self.announce_sender.clone(),
		}
	}
}

fn localized_payload<E: Encode>(round: RoundNumber, set_id: SetIdNumber, message: &E) -> Vec<u8> {
	(message, round, set_id).encode()
}

/// Type-safe wrapper around a round number.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct Round(pub RoundNumber);

/// Type-safe wrapper around a set ID.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct SetId(pub SetIdNumber);

// check a message.
pub(crate) fn check_message_sig<Block: BlockT>(
	message: &Message<Block>,
	id: &AuthorityId,
	signature: &AuthoritySignature,
	round: RoundNumber,
	set_id: SetIdNumber,
) -> Result<(), ()> {
	let as_public = id.clone();
	let encoded_raw = localized_payload(round, set_id, message);
	if AuthorityPair::verify(signature, &encoded_raw, &as_public) {
		Ok(())
	} else {
		debug!(target: "afg", "Bad signature on message from {:?}", id);
		Err(())
	}
}

/// A sink for outgoing messages to the network. Any messages that are sent will
/// be replaced, as appropriate, according to the given `HasVoted`.
/// NOTE: The votes are stored unsigned, which means that the signatures need to
/// be "stable", i.e. we should end up with the exact same signed message if we
/// use the same raw message and key to sign. This is currently true for
/// `ed25519` and `BLS` signatures (which we might use in the future), care must
/// be taken when switching to different key types.
struct OutgoingMessages<Block: BlockT, N: Network<Block>> {
	round: RoundNumber,
	set_id: SetIdNumber,
	locals: Option<(AuthorityPair, AuthorityId)>,
	sender: mpsc::UnboundedSender<SignedMessage<Block>>,
	announce_sender: periodic::BlockAnnounceSender<Block>,
	network: N,
	has_voted: HasVoted<Block>,
}

impl<Block: BlockT, N: Network<Block>> Sink for OutgoingMessages<Block, N>
{
	type SinkItem = Message<Block>;
	type SinkError = Error;

	fn start_send(&mut self, mut msg: Message<Block>) -> StartSend<Message<Block>, Error> {
		// if we've voted on this round previously under the same key, send that vote instead
		match &mut msg {
			grandpa::Message::PrimaryPropose(ref mut vote) =>
				if let Some(propose) = self.has_voted.propose() {
					*vote = propose.clone();
				},
			grandpa::Message::Prevote(ref mut vote) =>
				if let Some(prevote) = self.has_voted.prevote() {
					*vote = prevote.clone();
				},
			grandpa::Message::Precommit(ref mut vote) =>
				if let Some(precommit) = self.has_voted.precommit() {
					*vote = precommit.clone();
				},
		}

		// when locals exist, sign messages on import
		if let Some((ref pair, ref local_id)) = self.locals {
			let encoded = localized_payload(self.round, self.set_id, &msg);
			let signature = pair.sign(&encoded[..]);

			let target_hash = msg.target().0.clone();
			let signed = SignedMessage::<Block> {
				message: msg,
				signature,
				id: local_id.clone(),
			};

			let message = GossipMessage::VoteOrPrecommit(VoteOrPrecommitMessage::<Block> {
				message: signed.clone(),
				round: Round(self.round),
				set_id: SetId(self.set_id),
			});

			debug!(
				target: "afg",
				"Announcing block {} to peers which we voted on in round {} in set {}",
				target_hash,
				self.round,
				self.set_id,
			);

			telemetry!(
				CONSENSUS_DEBUG; "afg.announcing_blocks_to_voted_peers";
				"block" => ?target_hash, "round" => ?self.round, "set_id" => ?self.set_id,
			);

			// send the target block hash to the background block announcer
			self.announce_sender.send(target_hash, Vec::new());

			// propagate the message to peers
			let topic = round_topic::<Block>(self.round, self.set_id);
			self.network.gossip_message(topic, message.encode(), false);

			// forward the message to the inner sender.
			let _ = self.sender.unbounded_send(signed);
		}

		Ok(AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }

	fn close(&mut self) -> Poll<(), Error> {
		// ignore errors since we allow this inner sender to be closed already.
		self.sender.close().or_else(|_| Ok(Async::Ready(())))
	}
}

// checks a compact commit. returns the cost associated with processing it if
// the commit was bad.
fn check_compact_commit<Block: BlockT>(
	msg: &CompactCommit<Block>,
	voters: &VoterSet<AuthorityId>,
	round: Round,
	set_id: SetId,
) -> Result<(), i32> {
	// 4f + 1 = equivocations from f voters.
	let f = voters.total_weight() - voters.threshold();
	let full_threshold = voters.total_weight() + f;

	// check total weight is not out of range.
	let mut total_weight = 0;
	for (_, ref id) in &msg.auth_data {
		if let Some(weight) = voters.info(id).map(|info| info.weight()) {
			total_weight += weight;
			if total_weight > full_threshold {
				return Err(cost::MALFORMED_COMMIT);
			}
		} else {
			debug!(target: "afg", "Skipping commit containing unknown voter {}", id);
			return Err(cost::MALFORMED_COMMIT);
		}
	}

	if total_weight < voters.threshold() {
		return Err(cost::MALFORMED_COMMIT);
	}

	// check signatures on all contained precommits.
	for (i, (precommit, &(ref sig, ref id))) in msg.precommits.iter()
		.zip(&msg.auth_data)
		.enumerate()
	{
		use crate::communication::gossip::Misbehavior;
		use grandpa::Message as GrandpaMessage;

		if let Err(()) = check_message_sig::<Block>(
			&GrandpaMessage::Precommit(precommit.clone()),
			id,
			sig,
			round.0,
			set_id.0,
		) {
			debug!(target: "afg", "Bad commit message signature {}", id);
			telemetry!(CONSENSUS_DEBUG; "afg.bad_commit_msg_signature"; "id" => ?id);
			let cost = Misbehavior::BadCommitMessage {
				signatures_checked: i as i32,
				blocks_loaded: 0,
				equivocations_caught: 0,
			}.cost();

			return Err(cost);
		}
	}

	Ok(())
}

// checks a catch up. returns the cost associated with processing it if
// the catch up was bad.
fn check_catch_up<Block: BlockT>(
	msg: &CatchUp<Block>,
	voters: &VoterSet<AuthorityId>,
	set_id: SetId,
) -> Result<(), i32> {
	// 4f + 1 = equivocations from f voters.
	let f = voters.total_weight() - voters.threshold();
	let full_threshold = voters.total_weight() + f;

	// check total weight is not out of range for a set of votes.
	fn check_weight<'a>(
		voters: &'a VoterSet<AuthorityId>,
		votes: impl Iterator<Item=&'a AuthorityId>,
		full_threshold: u64,
	) -> Result<(), i32> {
		let mut total_weight = 0;

		for id in votes {
			if let Some(weight) = voters.info(&id).map(|info| info.weight()) {
				total_weight += weight;
				if total_weight > full_threshold {
					return Err(cost::MALFORMED_CATCH_UP);
				}
			} else {
				debug!(target: "afg", "Skipping catch up message containing unknown voter {}", id);
				return Err(cost::MALFORMED_CATCH_UP);
			}
		}

		if total_weight < voters.threshold() {
			return Err(cost::MALFORMED_CATCH_UP);
		}

		Ok(())
	};

	check_weight(
		voters,
		msg.prevotes.iter().map(|vote| &vote.id),
		full_threshold,
	)?;

	check_weight(
		voters,
		msg.precommits.iter().map(|vote| &vote.id),
		full_threshold,
	)?;

	fn check_signatures<'a, B, I>(
		messages: I,
		round: RoundNumber,
		set_id: SetIdNumber,
		mut signatures_checked: usize,
	) -> Result<usize, i32> where
		B: BlockT,
		I: Iterator<Item=(Message<B>, &'a AuthorityId, &'a AuthoritySignature)>,
	{
		use crate::communication::gossip::Misbehavior;

		for (msg, id, sig) in messages {
			signatures_checked += 1;

			if let Err(()) = check_message_sig::<B>(
				&msg,
				id,
				sig,
				round,
				set_id,
			) {
				debug!(target: "afg", "Bad catch up message signature {}", id);
				telemetry!(CONSENSUS_DEBUG; "afg.bad_catch_up_msg_signature"; "id" => ?id);

				let cost = Misbehavior::BadCatchUpMessage {
					signatures_checked: signatures_checked as i32,
				}.cost();

				return Err(cost);
			}
		}

		Ok(signatures_checked)
	}

	// check signatures on all contained prevotes.
	let signatures_checked = check_signatures::<Block, _>(
		msg.prevotes.iter().map(|vote| {
			(grandpa::Message::Prevote(vote.prevote.clone()), &vote.id, &vote.signature)
		}),
		msg.round_number,
		set_id.0,
		0,
	)?;

	// check signatures on all contained precommits.
	let _ = check_signatures::<Block, _>(
		msg.precommits.iter().map(|vote| {
			(grandpa::Message::Precommit(vote.precommit.clone()), &vote.id, &vote.signature)
		}),
		msg.round_number,
		set_id.0,
		signatures_checked,
	)?;

	Ok(())
}

/// An output sink for commit messages.
struct CommitsOut<Block: BlockT, N: Network<Block>> {
	network: N,
	set_id: SetId,
	is_voter: bool,
	gossip_validator: Arc<GossipValidator<Block>>,
	neighbor_sender: periodic::NeighborPacketSender<Block>,
}

impl<Block: BlockT, N: Network<Block>> CommitsOut<Block, N> {
	/// Create a new commit output stream.
	pub(crate) fn new(
		network: N,
		set_id: SetIdNumber,
		is_voter: bool,
		gossip_validator: Arc<GossipValidator<Block>>,
		neighbor_sender: periodic::NeighborPacketSender<Block>,
	) -> Self {
		CommitsOut {
			network,
			set_id: SetId(set_id),
			is_voter,
			gossip_validator,
			neighbor_sender,
		}
	}
}

impl<Block: BlockT, N: Network<Block>> Sink for CommitsOut<Block, N> {
	type SinkItem = (RoundNumber, Commit<Block>);
	type SinkError = Error;

	fn start_send(&mut self, input: (RoundNumber, Commit<Block>)) -> StartSend<Self::SinkItem, Error> {
		if !self.is_voter {
			return Ok(AsyncSink::Ready);
		}

		let (round, commit) = input;
		let round = Round(round);

		telemetry!(CONSENSUS_DEBUG; "afg.commit_issued";
			"target_number" => ?commit.target_number, "target_hash" => ?commit.target_hash,
		);
		let (precommits, auth_data) = commit.precommits.into_iter()
			.map(|signed| (signed.precommit, (signed.signature, signed.id)))
			.unzip();

		let compact_commit = CompactCommit::<Block> {
			target_hash: commit.target_hash,
			target_number: commit.target_number,
			precommits,
			auth_data
		};

		let message = GossipMessage::Commit(FullCommitMessage::<Block> {
			round: round,
			set_id: self.set_id,
			message: compact_commit,
		});

		let topic = global_topic::<Block>(self.set_id.0);

		// the gossip validator needs to be made aware of the best commit-height we know of
		// before gossiping
		self.gossip_validator.note_commit_finalized(
			commit.target_number,
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);
		self.network.gossip_message(topic, message.encode(), false);

		Ok(AsyncSink::Ready)
	}

	fn close(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
	fn poll_complete(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
}
