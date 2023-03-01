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

use futures::{channel::mpsc, prelude::*};
use log::{debug, trace};
use parking_lot::Mutex;
use prometheus_endpoint::Registry;
use std::{
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};

use finality_grandpa::{
	voter,
	voter_set::VoterSet,
	Message::{Precommit, Prevote, PrimaryPropose},
};
use parity_scale_codec::{Decode, Encode};
use sc_network::ReputationChange;
use sc_network_gossip::{GossipEngine, Network as GossipNetwork};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_INFO};
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, NumberFor};

use crate::{
	environment::HasVoted, CatchUp, Commit, CommunicationIn, CommunicationOutH, CompactCommit,
	Error, Message, SignedMessage, LOG_TARGET,
};
use gossip::{
	FullCatchUpMessage, FullCommitMessage, GossipMessage, GossipValidator, PeerReport, VoteMessage,
};
use sc_network_common::service::{NetworkBlock, NetworkSyncForkRequest};
use sc_utils::mpsc::TracingUnboundedReceiver;
use sp_consensus_grandpa::{AuthorityId, AuthoritySignature, RoundNumber, SetId as SetIdNumber};

pub mod gossip;
mod periodic;

#[cfg(test)]
pub(crate) mod tests;

// How often to rebroadcast neighbor packets, in cases where no new packets are created.
pub(crate) const NEIGHBOR_REBROADCAST_PERIOD: Duration = Duration::from_secs(2 * 60);

pub mod grandpa_protocol_name {
	use sc_chain_spec::ChainSpec;
	use sc_network_common::protocol::ProtocolName;

	pub(crate) const NAME: &str = "/grandpa/1";
	/// Old names for the notifications protocol, used for backward compatibility.
	pub(crate) const LEGACY_NAMES: [&str; 1] = ["/paritytech/grandpa/1"];

	/// Name of the notifications protocol used by GRANDPA.
	///
	/// Must be registered towards the networking in order for GRANDPA to properly function.
	pub fn standard_name<Hash: AsRef<[u8]>>(
		genesis_hash: &Hash,
		chain_spec: &Box<dyn ChainSpec>,
	) -> ProtocolName {
		let genesis_hash = genesis_hash.as_ref();
		let chain_prefix = match chain_spec.fork_id() {
			Some(fork_id) => format!("/{}/{}", array_bytes::bytes2hex("", genesis_hash), fork_id),
			None => format!("/{}", array_bytes::bytes2hex("", genesis_hash)),
		};
		format!("{}{}", chain_prefix, NAME).into()
	}
}

// cost scalars for reporting peers.
mod cost {
	use sc_network::ReputationChange as Rep;
	pub(super) const PAST_REJECTION: Rep = Rep::new(-50, "Grandpa: Past message");
	pub(super) const BAD_SIGNATURE: Rep = Rep::new(-100, "Grandpa: Bad signature");
	pub(super) const MALFORMED_CATCH_UP: Rep = Rep::new(-1000, "Grandpa: Malformed cath-up");
	pub(super) const MALFORMED_COMMIT: Rep = Rep::new(-1000, "Grandpa: Malformed commit");
	pub(super) const FUTURE_MESSAGE: Rep = Rep::new(-500, "Grandpa: Future message");
	pub(super) const UNKNOWN_VOTER: Rep = Rep::new(-150, "Grandpa: Unknown voter");

	pub(super) const INVALID_VIEW_CHANGE: Rep = Rep::new(-500, "Grandpa: Invalid view change");
	pub(super) const DUPLICATE_NEIGHBOR_MESSAGE: Rep =
		Rep::new(-500, "Grandpa: Duplicate neighbor message without grace period");
	pub(super) const PER_UNDECODABLE_BYTE: i32 = -5;
	pub(super) const PER_SIGNATURE_CHECKED: i32 = -25;
	pub(super) const PER_BLOCK_LOADED: i32 = -10;
	pub(super) const INVALID_CATCH_UP: Rep = Rep::new(-5000, "Grandpa: Invalid catch-up");
	pub(super) const INVALID_COMMIT: Rep = Rep::new(-5000, "Grandpa: Invalid commit");
	pub(super) const OUT_OF_SCOPE_MESSAGE: Rep = Rep::new(-500, "Grandpa: Out-of-scope message");
	pub(super) const CATCH_UP_REQUEST_TIMEOUT: Rep =
		Rep::new(-200, "Grandpa: Catch-up request timeout");

	// cost of answering a catch up request
	pub(super) const CATCH_UP_REPLY: Rep = Rep::new(-200, "Grandpa: Catch-up reply");
	pub(super) const HONEST_OUT_OF_SCOPE_CATCH_UP: Rep =
		Rep::new(-200, "Grandpa: Out-of-scope catch-up");
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

/// A type that ties together our local authority id and a keystore where it is
/// available for signing.
pub struct LocalIdKeystore((AuthorityId, SyncCryptoStorePtr));

impl LocalIdKeystore {
	/// Returns a reference to our local authority id.
	fn local_id(&self) -> &AuthorityId {
		&(self.0).0
	}

	/// Returns a reference to the keystore.
	fn keystore(&self) -> SyncCryptoStorePtr {
		(self.0).1.clone()
	}
}

impl From<(AuthorityId, SyncCryptoStorePtr)> for LocalIdKeystore {
	fn from(inner: (AuthorityId, SyncCryptoStorePtr)) -> LocalIdKeystore {
		LocalIdKeystore(inner)
	}
}

/// If the voter set is larger than this value some telemetry events are not
/// sent to avoid increasing usage resource on the node and flooding the
/// telemetry server (e.g. received votes, received commits.)
const TELEMETRY_VOTERS_LIMIT: usize = 10;

/// A handle to the network.
///
/// Something that provides both the capabilities needed for the `gossip_network::Network` trait as
/// well as the ability to set a fork sync request for a particular block.
pub trait Network<Block: BlockT>:
	NetworkSyncForkRequest<Block::Hash, NumberFor<Block>>
	+ NetworkBlock<Block::Hash, NumberFor<Block>>
	+ GossipNetwork<Block>
	+ Clone
	+ Send
	+ 'static
{
}

impl<Block, T> Network<Block> for T
where
	Block: BlockT,
	T: NetworkSyncForkRequest<Block::Hash, NumberFor<Block>>
		+ NetworkBlock<Block::Hash, NumberFor<Block>>
		+ GossipNetwork<Block>
		+ Clone
		+ Send
		+ 'static,
{
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
	gossip_engine: Arc<Mutex<GossipEngine<B>>>,
	validator: Arc<GossipValidator<B>>,

	/// Sender side of the neighbor packet channel.
	///
	/// Packets sent into this channel are processed by the `NeighborPacketWorker` and passed on to
	/// the underlying `GossipEngine`.
	neighbor_sender: periodic::NeighborPacketSender<B>,

	/// `NeighborPacketWorker` processing packets sent through the `NeighborPacketSender`.
	// `NetworkBridge` is required to be cloneable, thus one needs to be able to clone its
	// children, thus one has to wrap `neighbor_packet_worker` with an `Arc` `Mutex`.
	neighbor_packet_worker: Arc<Mutex<periodic::NeighborPacketWorker<B>>>,

	/// Receiver side of the peer report stream populated by the gossip validator, forwarded to the
	/// gossip engine.
	// `NetworkBridge` is required to be cloneable, thus one needs to be able to clone its
	// children, thus one has to wrap gossip_validator_report_stream with an `Arc` `Mutex`. Given
	// that it is just an `UnboundedReceiver`, one could also switch to a
	// multi-producer-*multi*-consumer channel implementation.
	gossip_validator_report_stream: Arc<Mutex<TracingUnboundedReceiver<PeerReport>>>,

	telemetry: Option<TelemetryHandle>,
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
		prometheus_registry: Option<&Registry>,
		telemetry: Option<TelemetryHandle>,
	) -> Self {
		let protocol = config.protocol_name.clone();
		let (validator, report_stream) =
			GossipValidator::new(config, set_state.clone(), prometheus_registry, telemetry.clone());

		let validator = Arc::new(validator);
		let gossip_engine = Arc::new(Mutex::new(GossipEngine::new(
			service.clone(),
			protocol,
			validator.clone(),
			prometheus_registry,
		)));

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
					let message = gossip::GossipMessage::Vote(gossip::VoteMessage::<B> {
						message: signed.clone(),
						round: Round(round.number),
						set_id: SetId(set_id),
					});

					gossip_engine.lock().register_gossip_message(topic, message.encode());
				}

				trace!(
					target: LOG_TARGET,
					"Registered {} messages for topic {:?} (round: {}, set_id: {})",
					round.votes.len(),
					topic,
					round.number,
					set_id,
				);
			}
		}

		let (neighbor_packet_worker, neighbor_packet_sender) =
			periodic::NeighborPacketWorker::new(NEIGHBOR_REBROADCAST_PERIOD);

		NetworkBridge {
			service,
			gossip_engine,
			validator,
			neighbor_sender: neighbor_packet_sender,
			neighbor_packet_worker: Arc::new(Mutex::new(neighbor_packet_worker)),
			gossip_validator_report_stream: Arc::new(Mutex::new(report_stream)),
			telemetry,
		}
	}

	/// Note the beginning of a new round to the `GossipValidator`.
	pub(crate) fn note_round(&self, round: Round, set_id: SetId, voters: &VoterSet<AuthorityId>) {
		// is a no-op if currently in that set.
		self.validator.note_set(
			set_id,
			voters.iter().map(|(v, _)| v.clone()).collect(),
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);

		self.validator
			.note_round(round, |to, neighbor| self.neighbor_sender.send(to, neighbor));
	}

	/// Get a stream of signature-checked round messages from the network as well as a sink for
	/// round messages to the network all within the current set.
	pub(crate) fn round_communication(
		&self,
		keystore: Option<LocalIdKeystore>,
		round: Round,
		set_id: SetId,
		voters: Arc<VoterSet<AuthorityId>>,
		has_voted: HasVoted<B::Header>,
	) -> (impl Stream<Item = SignedMessage<B::Header>> + Unpin, OutgoingMessages<B>) {
		self.note_round(round, set_id, &voters);

		let keystore = keystore.and_then(|ks| {
			let id = ks.local_id();
			if voters.contains(id) {
				Some(ks)
			} else {
				None
			}
		});

		let topic = round_topic::<B>(round.0, set_id.0);
		let telemetry = self.telemetry.clone();
		let incoming =
			self.gossip_engine.lock().messages_for(topic).filter_map(move |notification| {
				let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);

				match decoded {
					Err(ref e) => {
						debug!(
							target: LOG_TARGET,
							"Skipping malformed message {:?}: {}", notification, e
						);
						future::ready(None)
					},
					Ok(GossipMessage::Vote(msg)) => {
						// check signature.
						if !voters.contains(&msg.message.id) {
							debug!(
								target: LOG_TARGET,
								"Skipping message from unknown voter {}", msg.message.id
							);
							return future::ready(None)
						}

						if voters.len().get() <= TELEMETRY_VOTERS_LIMIT {
							match &msg.message.message {
								PrimaryPropose(propose) => {
									telemetry!(
										telemetry;
										CONSENSUS_INFO;
										"afg.received_propose";
										"voter" => ?format!("{}", msg.message.id),
										"target_number" => ?propose.target_number,
										"target_hash" => ?propose.target_hash,
									);
								},
								Prevote(prevote) => {
									telemetry!(
										telemetry;
										CONSENSUS_INFO;
										"afg.received_prevote";
										"voter" => ?format!("{}", msg.message.id),
										"target_number" => ?prevote.target_number,
										"target_hash" => ?prevote.target_hash,
									);
								},
								Precommit(precommit) => {
									telemetry!(
										telemetry;
										CONSENSUS_INFO;
										"afg.received_precommit";
										"voter" => ?format!("{}", msg.message.id),
										"target_number" => ?precommit.target_number,
										"target_hash" => ?precommit.target_hash,
									);
								},
							};
						}

						future::ready(Some(msg.message))
					},
					_ => {
						debug!(target: LOG_TARGET, "Skipping unknown message type");
						future::ready(None)
					},
				}
			});

		let (tx, out_rx) = mpsc::channel(0);
		let outgoing = OutgoingMessages::<B> {
			keystore,
			round: round.0,
			set_id: set_id.0,
			network: self.gossip_engine.clone(),
			sender: tx,
			has_voted,
			telemetry: self.telemetry.clone(),
		};

		// Combine incoming votes from external GRANDPA nodes with outgoing
		// votes from our own GRANDPA voter to have a single
		// vote-import-pipeline.
		let incoming = stream::select(incoming, out_rx);

		(incoming, outgoing)
	}

	/// Set up the global communication streams.
	pub(crate) fn global_communication(
		&self,
		set_id: SetId,
		voters: Arc<VoterSet<AuthorityId>>,
		is_voter: bool,
	) -> (
		impl Stream<Item = CommunicationIn<B>>,
		impl Sink<CommunicationOutH<B, B::Hash>, Error = Error> + Unpin,
	) {
		self.validator.note_set(
			set_id,
			voters.iter().map(|(v, _)| v.clone()).collect(),
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);

		let topic = global_topic::<B>(set_id.0);
		let incoming = incoming_global(
			self.gossip_engine.clone(),
			topic,
			voters,
			self.validator.clone(),
			self.neighbor_sender.clone(),
			self.telemetry.clone(),
		);

		let outgoing = CommitsOut::<B>::new(
			self.gossip_engine.clone(),
			set_id.0,
			is_voter,
			self.validator.clone(),
			self.neighbor_sender.clone(),
			self.telemetry.clone(),
		);

		let outgoing = outgoing.with(|out| {
			let voter::CommunicationOut::Commit(round, commit) = out;
			future::ok((round, commit))
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
		number: NumberFor<B>,
	) {
		self.service.set_sync_fork_request(peers, hash, number)
	}
}

impl<B: BlockT, N: Network<B>> Future for NetworkBridge<B, N> {
	type Output = Result<(), Error>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		loop {
			match self.neighbor_packet_worker.lock().poll_next_unpin(cx) {
				Poll::Ready(Some((to, packet))) => {
					self.gossip_engine.lock().send_message(to, packet.encode());
				},
				Poll::Ready(None) =>
					return Poll::Ready(Err(Error::Network(
						"Neighbor packet worker stream closed.".into(),
					))),
				Poll::Pending => break,
			}
		}

		loop {
			match self.gossip_validator_report_stream.lock().poll_next_unpin(cx) {
				Poll::Ready(Some(PeerReport { who, cost_benefit })) => {
					self.gossip_engine.lock().report(who, cost_benefit);
				},
				Poll::Ready(None) =>
					return Poll::Ready(Err(Error::Network(
						"Gossip validator report stream closed.".into(),
					))),
				Poll::Pending => break,
			}
		}

		match self.gossip_engine.lock().poll_unpin(cx) {
			Poll::Ready(()) =>
				return Poll::Ready(Err(Error::Network("Gossip engine future finished.".into()))),
			Poll::Pending => {},
		}

		Poll::Pending
	}
}

fn incoming_global<B: BlockT>(
	gossip_engine: Arc<Mutex<GossipEngine<B>>>,
	topic: B::Hash,
	voters: Arc<VoterSet<AuthorityId>>,
	gossip_validator: Arc<GossipValidator<B>>,
	neighbor_sender: periodic::NeighborPacketSender<B>,
	telemetry: Option<TelemetryHandle>,
) -> impl Stream<Item = CommunicationIn<B>> {
	let process_commit = {
		let telemetry = telemetry.clone();
		move |msg: FullCommitMessage<B>,
		      mut notification: sc_network_gossip::TopicNotification,
		      gossip_engine: &Arc<Mutex<GossipEngine<B>>>,
		      gossip_validator: &Arc<GossipValidator<B>>,
		      voters: &VoterSet<AuthorityId>| {
			if voters.len().get() <= TELEMETRY_VOTERS_LIMIT {
				let precommits_signed_by: Vec<String> =
					msg.message.auth_data.iter().map(move |(_, a)| format!("{}", a)).collect();

				telemetry!(
					telemetry;
					CONSENSUS_INFO;
					"afg.received_commit";
					"contains_precommits_signed_by" => ?precommits_signed_by,
					"target_number" => ?msg.message.target_number.clone(),
					"target_hash" => ?msg.message.target_hash.clone(),
				);
			}

			if let Err(cost) = check_compact_commit::<B>(
				&msg.message,
				voters,
				msg.round,
				msg.set_id,
				telemetry.as_ref(),
			) {
				if let Some(who) = notification.sender {
					gossip_engine.lock().report(who, cost);
				}

				return None
			}

			let round = msg.round;
			let set_id = msg.set_id;
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
						round,
						set_id,
						finalized_number,
						|to, neighbor| neighbor_sender.send(to, neighbor),
					);

					gossip_engine.lock().gossip_message(topic, notification.message.clone(), false);
				},
				voter::CommitProcessingOutcome::Bad(_) => {
					// report peer and do not gossip.
					if let Some(who) = notification.sender.take() {
						gossip_engine.lock().report(who, cost::INVALID_COMMIT);
					}
				},
			};

			let cb = voter::Callback::Work(Box::new(cb));

			Some(voter::CommunicationIn::Commit(round.0, commit, cb))
		}
	};

	let process_catch_up = move |msg: FullCatchUpMessage<B>,
	                             mut notification: sc_network_gossip::TopicNotification,
	                             gossip_engine: &Arc<Mutex<GossipEngine<B>>>,
	                             gossip_validator: &Arc<GossipValidator<B>>,
	                             voters: &VoterSet<AuthorityId>| {
		let gossip_validator = gossip_validator.clone();
		let gossip_engine = gossip_engine.clone();

		if let Err(cost) = check_catch_up::<B>(&msg.message, voters, msg.set_id, telemetry.clone())
		{
			if let Some(who) = notification.sender {
				gossip_engine.lock().report(who, cost);
			}

			return None
		}

		let cb = move |outcome| {
			if let voter::CatchUpProcessingOutcome::Bad(_) = outcome {
				// report peer
				if let Some(who) = notification.sender.take() {
					gossip_engine.lock().report(who, cost::INVALID_CATCH_UP);
				}
			}

			gossip_validator.note_catch_up_message_processed();
		};

		let cb = voter::Callback::Work(Box::new(cb));

		Some(voter::CommunicationIn::CatchUp(msg.message, cb))
	};

	gossip_engine
		.clone()
		.lock()
		.messages_for(topic)
		.filter_map(|notification| {
			// this could be optimized by decoding piecewise.
			let decoded = GossipMessage::<B>::decode(&mut &notification.message[..]);
			if let Err(ref e) = decoded {
				trace!(
					target: LOG_TARGET,
					"Skipping malformed commit message {:?}: {}",
					notification,
					e
				);
			}
			future::ready(decoded.map(move |d| (notification, d)).ok())
		})
		.filter_map(move |(notification, msg)| {
			future::ready(match msg {
				GossipMessage::Commit(msg) =>
					process_commit(msg, notification, &gossip_engine, &gossip_validator, &voters),
				GossipMessage::CatchUp(msg) =>
					process_catch_up(msg, notification, &gossip_engine, &gossip_validator, &voters),
				_ => {
					debug!(target: LOG_TARGET, "Skipping unknown message type");
					None
				},
			})
		})
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
			telemetry: self.telemetry.clone(),
		}
	}
}

/// Type-safe wrapper around a round number.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct Round(pub RoundNumber);

/// Type-safe wrapper around a set ID.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct SetId(pub SetIdNumber);

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
	keystore: Option<LocalIdKeystore>,
	sender: mpsc::Sender<SignedMessage<Block::Header>>,
	network: Arc<Mutex<GossipEngine<Block>>>,
	has_voted: HasVoted<Block::Header>,
	telemetry: Option<TelemetryHandle>,
}

impl<B: BlockT> Unpin for OutgoingMessages<B> {}

impl<Block: BlockT> Sink<Message<Block::Header>> for OutgoingMessages<Block> {
	type Error = Error;

	fn poll_ready(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		Sink::poll_ready(Pin::new(&mut self.sender), cx).map(|elem| {
			elem.map_err(|e| {
				Error::Network(format!("Failed to poll_ready channel sender: {:?}", e))
			})
		})
	}

	fn start_send(
		mut self: Pin<&mut Self>,
		mut msg: Message<Block::Header>,
	) -> Result<(), Self::Error> {
		// if we've voted on this round previously under the same key, send that vote instead
		match &mut msg {
			finality_grandpa::Message::PrimaryPropose(ref mut vote) => {
				if let Some(propose) = self.has_voted.propose() {
					*vote = propose.clone();
				}
			},
			finality_grandpa::Message::Prevote(ref mut vote) => {
				if let Some(prevote) = self.has_voted.prevote() {
					*vote = prevote.clone();
				}
			},
			finality_grandpa::Message::Precommit(ref mut vote) => {
				if let Some(precommit) = self.has_voted.precommit() {
					*vote = precommit.clone();
				}
			},
		}

		// when locals exist, sign messages on import
		if let Some(ref keystore) = self.keystore {
			let target_hash = *(msg.target().0);
			let signed = sp_consensus_grandpa::sign_message(
				keystore.keystore(),
				msg,
				keystore.local_id().clone(),
				self.round,
				self.set_id,
			)
			.ok_or_else(|| {
				Error::Signing(format!(
					"Failed to sign GRANDPA vote for round {} targetting {:?}",
					self.round, target_hash
				))
			})?;

			let message = GossipMessage::Vote(VoteMessage::<Block> {
				message: signed.clone(),
				round: Round(self.round),
				set_id: SetId(self.set_id),
			});

			debug!(
				target: LOG_TARGET,
				"Announcing block {} to peers which we voted on in round {} in set {}",
				target_hash,
				self.round,
				self.set_id,
			);

			telemetry!(
				self.telemetry;
				CONSENSUS_DEBUG;
				"afg.announcing_blocks_to_voted_peers";
				"block" => ?target_hash, "round" => ?self.round, "set_id" => ?self.set_id,
			);

			// announce the block we voted on to our peers.
			self.network.lock().announce(target_hash, None);

			// propagate the message to peers
			let topic = round_topic::<Block>(self.round, self.set_id);
			self.network.lock().gossip_message(topic, message.encode(), false);

			// forward the message to the inner sender.
			return self.sender.start_send(signed).map_err(|e| {
				Error::Network(format!("Failed to start_send on channel sender: {:?}", e))
			})
		};

		Ok(())
	}

	fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		Poll::Ready(Ok(()))
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		Sink::poll_close(Pin::new(&mut self.sender), cx).map(|elem| {
			elem.map_err(|e| {
				Error::Network(format!("Failed to poll_close channel sender: {:?}", e))
			})
		})
	}
}

// checks a compact commit. returns the cost associated with processing it if
// the commit was bad.
fn check_compact_commit<Block: BlockT>(
	msg: &CompactCommit<Block::Header>,
	voters: &VoterSet<AuthorityId>,
	round: Round,
	set_id: SetId,
	telemetry: Option<&TelemetryHandle>,
) -> Result<(), ReputationChange> {
	// 4f + 1 = equivocations from f voters.
	let f = voters.total_weight() - voters.threshold();
	let full_threshold = (f + voters.total_weight()).0;

	// check total weight is not out of range.
	let mut total_weight = 0;
	for (_, ref id) in &msg.auth_data {
		if let Some(weight) = voters.get(id).map(|info| info.weight()) {
			total_weight += weight.get();
			if total_weight > full_threshold {
				return Err(cost::MALFORMED_COMMIT)
			}
		} else {
			debug!(target: LOG_TARGET, "Skipping commit containing unknown voter {}", id);
			return Err(cost::MALFORMED_COMMIT)
		}
	}

	if total_weight < voters.threshold().get() {
		return Err(cost::MALFORMED_COMMIT)
	}

	// check signatures on all contained precommits.
	let mut buf = Vec::new();
	for (i, (precommit, &(ref sig, ref id))) in
		msg.precommits.iter().zip(&msg.auth_data).enumerate()
	{
		use crate::communication::gossip::Misbehavior;
		use finality_grandpa::Message as GrandpaMessage;

		if !sp_consensus_grandpa::check_message_signature_with_buffer(
			&GrandpaMessage::Precommit(precommit.clone()),
			id,
			sig,
			round.0,
			set_id.0,
			&mut buf,
		) {
			debug!(target: LOG_TARGET, "Bad commit message signature {}", id);
			telemetry!(
				telemetry;
				CONSENSUS_DEBUG;
				"afg.bad_commit_msg_signature";
				"id" => ?id,
			);
			let cost = Misbehavior::BadCommitMessage {
				signatures_checked: i as i32,
				blocks_loaded: 0,
				equivocations_caught: 0,
			}
			.cost();

			return Err(cost)
		}
	}

	Ok(())
}

// checks a catch up. returns the cost associated with processing it if
// the catch up was bad.
fn check_catch_up<Block: BlockT>(
	msg: &CatchUp<Block::Header>,
	voters: &VoterSet<AuthorityId>,
	set_id: SetId,
	telemetry: Option<TelemetryHandle>,
) -> Result<(), ReputationChange> {
	// 4f + 1 = equivocations from f voters.
	let f = voters.total_weight() - voters.threshold();
	let full_threshold = (f + voters.total_weight()).0;

	// check total weight is not out of range for a set of votes.
	fn check_weight<'a>(
		voters: &'a VoterSet<AuthorityId>,
		votes: impl Iterator<Item = &'a AuthorityId>,
		full_threshold: u64,
	) -> Result<(), ReputationChange> {
		let mut total_weight = 0;

		for id in votes {
			if let Some(weight) = voters.get(id).map(|info| info.weight()) {
				total_weight += weight.get();
				if total_weight > full_threshold {
					return Err(cost::MALFORMED_CATCH_UP)
				}
			} else {
				debug!(
					target: LOG_TARGET,
					"Skipping catch up message containing unknown voter {}", id
				);
				return Err(cost::MALFORMED_CATCH_UP)
			}
		}

		if total_weight < voters.threshold().get() {
			return Err(cost::MALFORMED_CATCH_UP)
		}

		Ok(())
	}

	check_weight(voters, msg.prevotes.iter().map(|vote| &vote.id), full_threshold)?;

	check_weight(voters, msg.precommits.iter().map(|vote| &vote.id), full_threshold)?;

	fn check_signatures<'a, B, I>(
		messages: I,
		round: RoundNumber,
		set_id: SetIdNumber,
		mut signatures_checked: usize,
		buf: &mut Vec<u8>,
		telemetry: Option<TelemetryHandle>,
	) -> Result<usize, ReputationChange>
	where
		B: BlockT,
		I: Iterator<Item = (Message<B::Header>, &'a AuthorityId, &'a AuthoritySignature)>,
	{
		use crate::communication::gossip::Misbehavior;

		for (msg, id, sig) in messages {
			signatures_checked += 1;

			if !sp_consensus_grandpa::check_message_signature_with_buffer(
				&msg, id, sig, round, set_id, buf,
			) {
				debug!(target: LOG_TARGET, "Bad catch up message signature {}", id);
				telemetry!(
					telemetry;
					CONSENSUS_DEBUG;
					"afg.bad_catch_up_msg_signature";
					"id" => ?id,
				);

				let cost = Misbehavior::BadCatchUpMessage {
					signatures_checked: signatures_checked as i32,
				}
				.cost();

				return Err(cost)
			}
		}

		Ok(signatures_checked)
	}

	let mut buf = Vec::new();

	// check signatures on all contained prevotes.
	let signatures_checked = check_signatures::<Block, _>(
		msg.prevotes.iter().map(|vote| {
			(finality_grandpa::Message::Prevote(vote.prevote.clone()), &vote.id, &vote.signature)
		}),
		msg.round_number,
		set_id.0,
		0,
		&mut buf,
		telemetry.clone(),
	)?;

	// check signatures on all contained precommits.
	let _ = check_signatures::<Block, _>(
		msg.precommits.iter().map(|vote| {
			(
				finality_grandpa::Message::Precommit(vote.precommit.clone()),
				&vote.id,
				&vote.signature,
			)
		}),
		msg.round_number,
		set_id.0,
		signatures_checked,
		&mut buf,
		telemetry,
	)?;

	Ok(())
}

/// An output sink for commit messages.
struct CommitsOut<Block: BlockT> {
	network: Arc<Mutex<GossipEngine<Block>>>,
	set_id: SetId,
	is_voter: bool,
	gossip_validator: Arc<GossipValidator<Block>>,
	neighbor_sender: periodic::NeighborPacketSender<Block>,
	telemetry: Option<TelemetryHandle>,
}

impl<Block: BlockT> CommitsOut<Block> {
	/// Create a new commit output stream.
	pub(crate) fn new(
		network: Arc<Mutex<GossipEngine<Block>>>,
		set_id: SetIdNumber,
		is_voter: bool,
		gossip_validator: Arc<GossipValidator<Block>>,
		neighbor_sender: periodic::NeighborPacketSender<Block>,
		telemetry: Option<TelemetryHandle>,
	) -> Self {
		CommitsOut {
			network,
			set_id: SetId(set_id),
			is_voter,
			gossip_validator,
			neighbor_sender,
			telemetry,
		}
	}
}

impl<Block: BlockT> Sink<(RoundNumber, Commit<Block::Header>)> for CommitsOut<Block> {
	type Error = Error;

	fn poll_ready(self: Pin<&mut Self>, _: &mut Context) -> Poll<Result<(), Self::Error>> {
		Poll::Ready(Ok(()))
	}

	fn start_send(
		self: Pin<&mut Self>,
		input: (RoundNumber, Commit<Block::Header>),
	) -> Result<(), Self::Error> {
		if !self.is_voter {
			return Ok(())
		}

		let (round, commit) = input;
		let round = Round(round);

		telemetry!(
			self.telemetry;
			CONSENSUS_DEBUG;
			"afg.commit_issued";
			"target_number" => ?commit.target_number,
			"target_hash" => ?commit.target_hash,
		);
		let (precommits, auth_data) = commit
			.precommits
			.into_iter()
			.map(|signed| (signed.precommit, (signed.signature, signed.id)))
			.unzip();

		let compact_commit = CompactCommit::<Block::Header> {
			target_hash: commit.target_hash,
			target_number: commit.target_number,
			precommits,
			auth_data,
		};

		let message = GossipMessage::Commit(FullCommitMessage::<Block> {
			round,
			set_id: self.set_id,
			message: compact_commit,
		});

		let topic = global_topic::<Block>(self.set_id.0);

		// the gossip validator needs to be made aware of the best commit-height we know of
		// before gossiping
		self.gossip_validator.note_commit_finalized(
			round,
			self.set_id,
			commit.target_number,
			|to, neighbor| self.neighbor_sender.send(to, neighbor),
		);
		self.network.lock().gossip_message(topic, message.encode(), false);

		Ok(())
	}

	fn poll_close(self: Pin<&mut Self>, _: &mut Context) -> Poll<Result<(), Self::Error>> {
		Poll::Ready(Ok(()))
	}

	fn poll_flush(self: Pin<&mut Self>, _: &mut Context) -> Poll<Result<(), Self::Error>> {
		Poll::Ready(Ok(()))
	}
}
