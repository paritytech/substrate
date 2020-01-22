// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use futures::prelude::*;
use futures03::{
	channel::mpsc as mpsc03,
	compat::Compat,
	future::{self as future03, Future as Future03},
	sink::Sink as Sink03,
	stream::{Stream as Stream03, StreamExt},
};
use log::{debug, trace};
use parking_lot::Mutex;
use std::{pin::Pin, sync::Arc, task::{Context, Poll as Poll03}};

use finality_grandpa::Message::{Prevote, Precommit, PrimaryPropose};
use finality_grandpa::{voter, voter_set::VoterSet};
use sc_network::{NetworkService, ReputationChange};
use sc_network_gossip::{GossipEngine, Network as GossipNetwork};
use parity_scale_codec::{Encode, Decode};
use sp_core::Pair;
use sp_runtime::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, NumberFor};
use sc_telemetry::{telemetry, CONSENSUS_DEBUG, CONSENSUS_INFO};

use crate::{
	CatchUp, Commit, CommunicationIn, CommunicationOut, CompactCommit, Error,
	Message, SignedMessage,
};
use crate::environment::HasVoted;
use gossip::{
	FullCatchUpMessage,
	FullCommitMessage,
	GossipMessage,
	GossipValidator,
	PeerReport,
	VoteMessage,
};
use sp_finality_grandpa::{
	AuthorityPair, AuthorityId, AuthoritySignature, SetId as SetIdNumber, RoundNumber,
};

pub mod gossip;
mod periodic;

#[cfg(test)]
mod tests;

pub use sp_finality_grandpa::GRANDPA_ENGINE_ID;

// cost scalars for reporting peers.
mod cost {
	use sc_network::ReputationChange as Rep;
	pub(super) const PAST_REJECTION: Rep = Rep::new(-50, "Grandpa: Past message");
	pub(super) const BAD_SIGNATURE: Rep = Rep::new(-100, "Grandpa: Bad signature");
	pub(super) const MALFORMED_CATCH_UP: Rep = Rep::new(-1000, "Grandpa: Malformed cath-up");
	pub(super) const MALFORMED_COMMIT: Rep = Rep::new(-1000, "Grandpa: Malformed commit");
	pub(super) const FUTURE_MESSAGE: Rep = Rep::new(-500, "Grandpa: Future message");
	pub(super) const UNKNOWN_VOTER: Rep = Rep::new(-150, "Grandpa: Uknown voter");

	pub(super) const INVALID_VIEW_CHANGE: Rep = Rep::new(-500, "Grandpa: Invalid view change");
	pub(super) const PER_UNDECODABLE_BYTE: i32 = -5;
	pub(super) const PER_SIGNATURE_CHECKED: i32 = -25;
	pub(super) const PER_BLOCK_LOADED: i32 = -10;
	pub(super) const INVALID_CATCH_UP: Rep = Rep::new(-5000, "Grandpa: Invalid catch-up");
	pub(super) const INVALID_COMMIT: Rep = Rep::new(-5000, "Grandpa: Invalid commit");
	pub(super) const OUT_OF_SCOPE_MESSAGE: Rep = Rep::new(-500, "Grandpa: Out-of-scope message");
	pub(super) const CATCH_UP_REQUEST_TIMEOUT: Rep = Rep::new(-200, "Grandpa: Catch-up reqeust timeout");

	// cost of answering a catch up request
	pub(super) const CATCH_UP_REPLY: Rep = Rep::new(-200, "Grandpa: Catch-up reply");
	pub(super) const HONEST_OUT_OF_SCOPE_CATCH_UP: Rep = Rep::new(-200, "Grandpa: Out-of-scope catch-up");
}

// benefit scalars for reporting peers.
mod benefit {
	use sc_network::ReputationChange as Rep;
	pub(super) const NEIGHBOR_MESSAGE: Rep = Rep::new(100, "Grandpa: Neighbor message");
	pub(super) const ROUND_MESSAGE: Rep = Rep::new(100, "Grandpa: Round message");
	pub(super) const BASIC_VALIDATED_CATCH_UP: Rep = Rep::new(200, "Grandpa: Catch-up message");
	pub(super) const BASIC_VALIDATED_COMMIT: Rep = Rep::new(100, "Grandpa: Commit");
	pub(super) const PER_EQUIVOCATION: i32 = 10;
}

/// A handle to the network.
///
/// Something that provides both the capabilities needed for the `gossip_network::Network` trait as
/// well as the ability to set a fork sync request for a particular block.
pub trait Network<Block: BlockT>: GossipNetwork<Block> + Clone + Send + 'static {
	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	fn set_sync_fork_request(&self, peers: Vec<sc_network::PeerId>, hash: Block::Hash, number: NumberFor<Block>);
}

impl<B, S, H> Network<B> for Arc<NetworkService<B, S, H>> where
	B: BlockT,
	S: sc_network::specialization::NetworkSpecialization<B>,
	H: sc_network::ExHashT,
{
	fn set_sync_fork_request(&self, peers: Vec<sc_network::PeerId>, hash: B::Hash, number: NumberFor<B>) {
		NetworkService::set_sync_fork_request(self, peers, hash, number)
	}
}

/// Create a unique topic for a round and set-id combo.
pub(crate) fn round_topic<B: BlockT>(round: RoundNumber, set_id: SetIdNumber) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-{}", set_id, round).as_bytes())
}

/// Create a unique topic for global messages on a set ID.
pub(crate) fn global_topic<B: BlockT>(set_id: SetIdNumber) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-GLOBAL", set_id).as_bytes())
}

/// Bridge between the underlying network service, gossiping consensus messages and Grandpa
pub(crate) struct NetworkBridge<B: BlockT, N: Network<B>> {
	service: N,
	gossip_engine: GossipEngine<B>,
	validator: Arc<GossipValidator<B>>,

	/// Sender side of the neighbor packet channel.
	///
	/// Packets sent into this channel are processed by the `NeighborPacketWorker` and passed on to
	/// the underlying `GossipEngine`.
	neighbor_sender: periodic::NeighborPacketSender<B>,

	/// `NeighborPacketWorker` processing packets sent through the `NeighborPacketSender`.
	//
	// `NetworkBridge` is required to be clonable, thus one needs to be able to clone its children,
	// thus one has to wrap neighor_packet_worker with an `Arc` `Mutex`.
	neighbor_packet_worker: Arc<Mutex<periodic::NeighborPacketWorker<B>>>,

	/// Receiver side of the peer report stream populated by the gossip validator, forwarded to the
	/// gossip engine.
	//
	// `NetworkBridge` is required to be clonable, thus one needs to be able to clone its children,
	// thus one has to wrap gossip_validator_report_stream with an `Arc` `Mutex`. Given that it is
	// just an `UnboundedReceiver`, one could also switch to a multi-producer-*multi*-consumer
	// channel implementation.
	gossip_validator_report_stream: Arc<Mutex<mpsc03::UnboundedReceiver<PeerReport>>>,
}

impl<B: BlockT, N: Network<B>> Unpin for NetworkBridge<B, N> {}

impl<B: BlockT, N: Network<B>> NetworkBridge<B, N> {
	/// Create a new NetworkBridge to the given NetworkService. Returns the service
	/// handle.
	/// On creation it will register previous rounds' votes with the gossip
	/// service taken from the VoterSetState.
	pub(crate) fn new(
		service: N,
		config: crate::Config,
		set_state: crate::environment::SharedVoterSetState<B>,
		executor: &impl futures03::task::Spawn,
	) -> Self {
		let (validator, report_stream) = GossipValidator::new(
			config,
			set_state.clone(),
		);

		let validator = Arc::new(validator);
		let gossip_engine = GossipEngine::new(service.clone(), executor, GRANDPA_ENGINE_ID, validator.clone());

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
					let message = gossip::GossipMessage::Vote(
						gossip::VoteMessage::<B> {
							message: signed.clone(),
							round: Round(round.number),
							set_id: SetId(set_id),
						}
					);

					gossip_engine.register_gossip_message(
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

		let (neighbor_packet_worker, neighbor_packet_sender) = periodic::NeighborPacketWorker::new();

		let bridge = NetworkBridge {
			service,
			gossip_engine,
			validator,
			neighbor_sender: neighbor_packet_sender,
			neighbor_packet_worker: Arc::new(Mutex::new(neighbor_packet_worker)),
			gossip_validator_report_stream: Arc::new(Mutex::new(report_stream)),
		};

		bridge
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

	/// Get a stream of signature-checked round messages from the network as well as a sink for round messages to the
	/// network all within the current set.
	pub(crate) fn round_communication(
		&self,
		round: Round,
		set_id: SetId,
		voters: Arc<VoterSet<AuthorityId>>,
		local_key: Option<AuthorityPair>,
		has_voted: HasVoted<B>,
	) -> (
		impl Stream03<Item=SignedMessage<B>> + Unpin,
		OutgoingMessages<B>,
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
		let incoming = self.gossip_engine.messages_for(topic)
			.filter_map(move |notification| {
				let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);

				match decoded {
					Err(ref e) => {
						debug!(target: "afg", "Skipping malformed message {:?}: {}", notification, e);
						return future03::ready(None);
					}
					Ok(GossipMessage::Vote(msg)) => {
						// check signature.
						if !voters.contains_key(&msg.message.id) {
							debug!(target: "afg", "Skipping message from unknown voter {}", msg.message.id);
							return future03::ready(None);
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

						future03::ready(Some(msg.message))
					}
					_ => {
						debug!(target: "afg", "Skipping unknown message type");
						return future03::ready(None);
					}
				}
			});

		let (tx, out_rx) = mpsc03::channel(0);
		let outgoing = OutgoingMessages::<B> {
			round: round.0,
			set_id: set_id.0,
			network: self.gossip_engine.clone(),
			locals,
			sender: tx,
			has_voted,
		};

		// Combine incoming votes from external GRANDPA nodes with outgoing
		// votes from our own GRANDPA voter to have a single
		// vote-import-pipeline.
		let incoming = futures03::stream::select(incoming, out_rx);

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

		let service = self.gossip_engine.clone();
		let topic = global_topic::<B>(set_id.0);
		let incoming = incoming_global(
			service,
			topic,
			voters,
			self.validator.clone(),
			self.neighbor_sender.clone(),
		);

		let outgoing = CommitsOut::<B>::new(
			self.gossip_engine.clone(),
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

	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	pub(crate) fn set_sync_fork_request(
		&self,
		peers: Vec<sc_network::PeerId>,
		hash: B::Hash,
		number: NumberFor<B>
	) {
		Network::set_sync_fork_request(&self.service, peers, hash, number)
	}
}

impl<B: BlockT, N: Network<B>> Future03 for NetworkBridge<B, N> {
	type Output = Result<(), Error>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll03<Self::Output> {
		loop {
			match self.neighbor_packet_worker.lock().poll_next_unpin(cx) {
				Poll03::Ready(Some((to, packet))) => {
					self.gossip_engine.send_message(to, packet.encode());
				},
				Poll03::Ready(None) => return Poll03::Ready(
					Err(Error::Network("Neighbor packet worker stream closed.".into()))
				),
				Poll03::Pending => break,
			}
		}

		loop {
			match self.gossip_validator_report_stream.lock().poll_next_unpin(cx) {
				Poll03::Ready(Some(PeerReport { who, cost_benefit })) => {
					self.gossip_engine.report(who, cost_benefit);
				},
				Poll03::Ready(None) => return Poll03::Ready(
					Err(Error::Network("Gossip validator report stream closed.".into()))
				),
				Poll03::Pending => break,
			}
		}

		Poll03::Pending
	}
}

fn incoming_global<B: BlockT>(
	mut gossip_engine: GossipEngine<B>,
	topic: B::Hash,
	voters: Arc<VoterSet<AuthorityId>>,
	gossip_validator: Arc<GossipValidator<B>>,
	neighbor_sender: periodic::NeighborPacketSender<B>,
) -> impl Stream<Item = CommunicationIn<B>, Error = Error> {
	let process_commit = move |
		msg: FullCommitMessage<B>,
		mut notification: sc_network_gossip::TopicNotification,
		gossip_engine: &mut GossipEngine<B>,
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
				gossip_engine.report(who, cost);
			}

			return None;
		}

		let round = msg.round.0;
		let commit = msg.message;
		let finalized_number = commit.target_number;
		let gossip_validator = gossip_validator.clone();
		let gossip_engine = gossip_engine.clone();
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

				gossip_engine.gossip_message(topic, notification.message.clone(), false);
			}
			voter::CommitProcessingOutcome::Bad(_) => {
				// report peer and do not gossip.
				if let Some(who) = notification.sender.take() {
					gossip_engine.report(who, cost::INVALID_COMMIT);
				}
			}
		};

		let cb = voter::Callback::Work(Box::new(cb));

		Some(voter::CommunicationIn::Commit(round, commit, cb))
	};

	let process_catch_up = move |
		msg: FullCatchUpMessage<B>,
		mut notification: sc_network_gossip::TopicNotification,
		gossip_engine: &mut GossipEngine<B>,
		gossip_validator: &Arc<GossipValidator<B>>,
		voters: &VoterSet<AuthorityId>,
	| {
		let gossip_validator = gossip_validator.clone();
		let gossip_engine = gossip_engine.clone();

		if let Err(cost) = check_catch_up::<B>(
			&msg.message,
			voters,
			msg.set_id,
		) {
			if let Some(who) = notification.sender {
				gossip_engine.report(who, cost);
			}

			return None;
		}

		let cb = move |outcome| {
			if let voter::CatchUpProcessingOutcome::Bad(_) = outcome {
				// report peer
				if let Some(who) = notification.sender.take() {
					gossip_engine.report(who, cost::INVALID_CATCH_UP);
				}
			}

			gossip_validator.note_catch_up_message_processed();
		};

		let cb = voter::Callback::Work(Box::new(cb));

		Some(voter::CommunicationIn::CatchUp(msg.message, cb))
	};

	Compat::new(gossip_engine.messages_for(topic)
		.map(|m| Ok::<_, ()>(m)))
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
					process_commit(msg, notification, &mut gossip_engine, &gossip_validator, &*voters),
				GossipMessage::CatchUp(msg) =>
					process_catch_up(msg, notification, &mut gossip_engine, &gossip_validator, &*voters),
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
			gossip_engine: self.gossip_engine.clone(),
			validator: Arc::clone(&self.validator),
			neighbor_sender: self.neighbor_sender.clone(),
			neighbor_packet_worker: self.neighbor_packet_worker.clone(),
			gossip_validator_report_stream: self.gossip_validator_report_stream.clone(),
		}
	}
}

pub(crate) fn localized_payload<E: Encode>(round: RoundNumber, set_id: SetIdNumber, message: &E) -> Vec<u8> {
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
pub(crate) struct OutgoingMessages<Block: BlockT> {
	round: RoundNumber,
	set_id: SetIdNumber,
	locals: Option<(AuthorityPair, AuthorityId)>,
	sender: mpsc03::Sender<SignedMessage<Block>>,
	network: GossipEngine<Block>,
	has_voted: HasVoted<Block>,
}

impl<B: BlockT> Unpin for OutgoingMessages<B> {}

impl<Block: BlockT> Sink03<Message<Block>> for OutgoingMessages<Block>
{
	type Error = Error;

	fn poll_ready(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll03<Result<(), Self::Error>> {
		Sink03::poll_ready(Pin::new(&mut self.sender), cx)
			.map(|elem| { elem.map_err(|e| {
				Error::Network(format!("Failed to poll_ready channel sender: {:?}", e))
			})})
	}

	fn start_send(mut self: Pin<&mut Self>, mut msg: Message<Block>) -> Result<(), Self::Error> {
		// if we've voted on this round previously under the same key, send that vote instead
		match &mut msg {
			finality_grandpa::Message::PrimaryPropose(ref mut vote) =>
				if let Some(propose) = self.has_voted.propose() {
					*vote = propose.clone();
				},
			finality_grandpa::Message::Prevote(ref mut vote) =>
				if let Some(prevote) = self.has_voted.prevote() {
					*vote = prevote.clone();
				},
			finality_grandpa::Message::Precommit(ref mut vote) =>
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

			let message = GossipMessage::Vote(VoteMessage::<Block> {
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

			// announce the block we voted on to our peers.
			self.network.announce(target_hash, Vec::new());

			// propagate the message to peers
			let topic = round_topic::<Block>(self.round, self.set_id);
			self.network.gossip_message(topic, message.encode(), false);

			// forward the message to the inner sender.
			return self.sender.start_send(signed).map_err(|e| {
				Error::Network(format!("Failed to start_send on channel sender: {:?}", e))
			});
		};

		Ok(())
	}

	fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context) -> Poll03<Result<(), Self::Error>> {
		Poll03::Ready(Ok(()))
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll03<Result<(), Self::Error>> {
		Sink03::poll_close(Pin::new(&mut self.sender), cx)
			.map(|elem| { elem.map_err(|e| {
				Error::Network(format!("Failed to poll_close channel sender: {:?}", e))
			})})
	}
}

// checks a compact commit. returns the cost associated with processing it if
// the commit was bad.
fn check_compact_commit<Block: BlockT>(
	msg: &CompactCommit<Block>,
	voters: &VoterSet<AuthorityId>,
	round: Round,
	set_id: SetId,
) -> Result<(), ReputationChange> {
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
		use finality_grandpa::Message as GrandpaMessage;

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
) -> Result<(), ReputationChange> {
	// 4f + 1 = equivocations from f voters.
	let f = voters.total_weight() - voters.threshold();
	let full_threshold = voters.total_weight() + f;

	// check total weight is not out of range for a set of votes.
	fn check_weight<'a>(
		voters: &'a VoterSet<AuthorityId>,
		votes: impl Iterator<Item=&'a AuthorityId>,
		full_threshold: u64,
	) -> Result<(), ReputationChange> {
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
	) -> Result<usize, ReputationChange> where
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
			(finality_grandpa::Message::Prevote(vote.prevote.clone()), &vote.id, &vote.signature)
		}),
		msg.round_number,
		set_id.0,
		0,
	)?;

	// check signatures on all contained precommits.
	let _ = check_signatures::<Block, _>(
		msg.precommits.iter().map(|vote| {
			(finality_grandpa::Message::Precommit(vote.precommit.clone()), &vote.id, &vote.signature)
		}),
		msg.round_number,
		set_id.0,
		signatures_checked,
	)?;

	Ok(())
}

/// An output sink for commit messages.
struct CommitsOut<Block: BlockT> {
	network: GossipEngine<Block>,
	set_id: SetId,
	is_voter: bool,
	gossip_validator: Arc<GossipValidator<Block>>,
	neighbor_sender: periodic::NeighborPacketSender<Block>,
}

impl<Block: BlockT> CommitsOut<Block> {
	/// Create a new commit output stream.
	pub(crate) fn new(
		network: GossipEngine<Block>,
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

impl<Block: BlockT> Sink for CommitsOut<Block> {
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
