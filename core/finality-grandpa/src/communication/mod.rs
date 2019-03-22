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

//! Incoming message streams that verify signatures, and outgoing message streams
//! that sign or re-shape.

use std::sync::Arc;

use grandpa::VoterSet;
use grandpa::Message::{Prevote, Precommit};
use futures::prelude::*;
use futures::sync::{oneshot, mpsc};
use log::{debug, trace};
use parity_codec::{Encode, Decode};
use substrate_primitives::{ed25519, Pair};
use substrate_telemetry::{telemetry, CONSENSUS_DEBUG, CONSENSUS_INFO};
use runtime_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, NumberFor};
use network::{consensus_gossip as network_gossip, ConsensusEngineId, Service as NetworkService,};

use crate::{Error, Message, SignedMessage, Commit, CompactCommit};
use gossip::{GossipMessage, FullCommitMessage, VoteOrPrecommitMessage, GossipValidator};
use substrate_primitives::ed25519::{Public as AuthorityId, Signature as AuthoritySignature};

pub mod gossip;

/// The consensus engine ID of GRANDPA.
pub const GRANDPA_ENGINE_ID: ConsensusEngineId = [b'a', b'f', b'g', b'1'];

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
pub trait Network<Block: BlockT>: Clone {
	/// A stream of input messages for a topic.
	type In: Stream<Item=network_gossip::TopicNotification,Error=()>;

	/// Get a stream of messages for a specific round. This stream should
	/// never logically conclude.
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In;

	/// Send a message at a specific round out.
	///
	/// Force causes it to be sent to all peers, even if they've seen it already.
	/// Only should be used in case of consensus stall.
	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>, force: bool);

	/// Get a stream of commit messages for a specific set-id. This stream
	/// should never logically conclude.
	fn commit_messages(&self, set_id: u64) -> Self::In;

	/// Send message over the commit channel.
	///
	/// Force causes it to be sent to all peers, even if they've seen it already.
	/// Only should be used in case of consensus stall.
	fn send_commit(&self, set_id: u64, message: Vec<u8>, force: bool);

	/// Inform peers that a block with given hash should be downloaded.
	fn announce(&self, round: u64, set_id: u64, block: Block::Hash);
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

/// Bridge between NetworkService, gossiping consensus messages and Grandpa
pub struct NetworkBridge<B: BlockT, S: network::specialization::NetworkSpecialization<B>> {
	service: Arc<NetworkService<B, S>>,
	validator: Arc<GossipValidator<B>>,
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>> NetworkBridge<B, S> {
	/// Create a new NetworkBridge to the given NetworkService
	pub fn new(service: Arc<NetworkService<B, S>>) -> Self {
		let validator = Arc::new(GossipValidator::new());
		let v = validator.clone();
		service.with_gossip(move |gossip, _| {
			gossip.register_validator(GRANDPA_ENGINE_ID, v);
		});
		NetworkBridge { service, validator: validator }
	}
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>,> Clone for NetworkBridge<B, S> {
	fn clone(&self) -> Self {
		NetworkBridge {
			service: Arc::clone(&self.service),
			validator: Arc::clone(&self.validator),
		}
	}
}

/// Create a unique topic for a round and set-id combo.
pub(crate) fn round_topic<B: BlockT>(round: u64, set_id: u64) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-{}", set_id, round).as_bytes())
}

/// Create a unique topic for global messages on a set ID.
pub(crate) fn global_topic<B: BlockT>(set_id: u64) -> B::Hash {
	<<B::Header as HeaderT>::Hashing as HashT>::hash(format!("{}-GLOBAL", set_id).as_bytes())
}

impl<B: BlockT, S: network::specialization::NetworkSpecialization<B>,> Network<B> for NetworkBridge<B, S> {
	type In = NetworkStream;
	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		self.validator.note_round(Round(round), SetId(set_id));
		let (tx, rx) = oneshot::channel();
		self.service.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(GRANDPA_ENGINE_ID, round_topic::<B>(round, set_id));
			let _ = tx.send(inner_rx);
		});
		NetworkStream { outer: rx, inner: None }
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>, force: bool) {
		let topic = round_topic::<B>(round, set_id);
		let recipient = if force {
			network_gossip::MessageRecipient::BroadcastToAll
		} else {
			network_gossip::MessageRecipient::BroadcastNew
		};
		self.service.gossip_consensus_message(topic, GRANDPA_ENGINE_ID, message, recipient);
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		self.validator.note_set(SetId(set_id));
		let (tx, rx) = oneshot::channel();
		self.service.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(GRANDPA_ENGINE_ID, global_topic::<B>(set_id));
			let _ = tx.send(inner_rx);
		});
		NetworkStream { outer: rx, inner: None }
	}

	fn send_commit(&self, set_id: u64, message: Vec<u8>, force: bool) {
		let topic = global_topic::<B>(set_id);
		let recipient = if force {
			network_gossip::MessageRecipient::BroadcastToAll
		} else {
			network_gossip::MessageRecipient::BroadcastNew
		};
		self.service.gossip_consensus_message(topic, GRANDPA_ENGINE_ID, message, recipient);
	}

	fn announce(&self, round: u64, _set_id: u64, block: B::Hash) {
		debug!(target: "afg", "Announcing block {} to peers which we voted on in round {}", block, round);
		telemetry!(CONSENSUS_DEBUG; "afg.announcing_blocks_to_voted_peers";
			"block" => ?block, "round" => ?round
		);
		self.service.announce_block(block)
	}
}

fn localized_payload<E: Encode>(round: u64, set_id: u64, message: &E) -> Vec<u8> {
	(message, round, set_id).encode()
}

/// Type-safe wrapper around u64 when indicating that it's a round number.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct Round(pub u64);

/// Type-safe wrapper around u64 when indicating that it's a set ID.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Encode, Decode)]
pub struct SetId(pub u64);

// check a message.
pub(crate) fn check_message_sig<Block: BlockT>(
	message: &Message<Block>,
	id: &AuthorityId,
	signature: &AuthoritySignature,
	round: u64,
	set_id: u64,
) -> Result<(), ()> {
	let as_public = AuthorityId::from_raw(id.0);
	let encoded_raw = localized_payload(round, set_id, message);
	if ed25519::Pair::verify(signature, &encoded_raw, as_public) {
		Ok(())
	} else {
		debug!(target: "afg", "Bad signature on message from {:?}", id);
		Err(())
	}
}

/// converts a message stream into a stream of signed messages.
/// the output stream assumes signatures have been checked already.
pub(crate) fn checked_message_stream<Block: BlockT, S>(
	inner: S,
	voters: Arc<VoterSet<AuthorityId>>,
)
	-> impl Stream<Item=SignedMessage<Block>,Error=Error> where
	S: Stream<Item=network_gossip::TopicNotification, Error=()>
{
	inner
		.filter_map(|notification| {
			let decoded = GossipMessage::<Block>::decode(&mut &notification.message[..]);
			if decoded.is_none() {
				debug!(target: "afg", "Skipping malformed message {:?}", notification);
			}
			decoded
		})
		.and_then(move |msg| {
			match msg {
				GossipMessage::VoteOrPrecommit(msg) => {
					// check signature.
					if !voters.contains_key(&msg.message.id) {
						debug!(target: "afg", "Skipping message from unknown voter {}", msg.message.id);
						return Ok(None);
					}

					println!("Got message {:?}", msg.message);

					match &msg.message.message {
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
		.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")))
}

/// Whether we've voted already during a prior run of the program.
#[derive(Decode, Encode)]
pub(crate) enum HasVoted {
	/// Has not voted already in this round.
	#[codec(index = "0")]
	No,
	/// Has cast a proposal.
	#[codec(index = "1")]
	Proposed,
	/// Has cast a prevote.
	#[codec(index = "2")]
	Prevoted,
	/// Has cast a precommit (implies prevote.)
	#[codec(index = "3")]
	Precommitted,
}

impl HasVoted {
	#[allow(unused)]
	fn can_propose(&self) -> bool {
		match *self {
			HasVoted::No => true,
			HasVoted::Proposed | HasVoted::Prevoted | HasVoted::Precommitted => false,
		}
	}

	fn can_prevote(&self) -> bool {
		match *self {
			HasVoted::No | HasVoted::Proposed => true,
			HasVoted::Prevoted | HasVoted::Precommitted => false,
		}
	}

	fn can_precommit(&self) -> bool {
		match *self {
			HasVoted::No | HasVoted::Proposed | HasVoted::Prevoted => true,
			HasVoted::Precommitted => false,
		}
	}
}

pub(crate) struct OutgoingMessages<Block: BlockT, N: Network<Block>> {
	round: u64,
	set_id: u64,
	locals: Option<(Arc<ed25519::Pair>, AuthorityId)>,
	sender: mpsc::UnboundedSender<SignedMessage<Block>>,
	network: N,
	has_voted: HasVoted,
}

impl<Block: BlockT, N: Network<Block>> Sink for OutgoingMessages<Block, N>
{
	type SinkItem = Message<Block>;
	type SinkError = Error;

	fn start_send(&mut self, msg: Message<Block>) -> StartSend<Message<Block>, Error> {
		// only sign if we haven't voted in this round already.
		let should_sign = match msg {
			grandpa::Message::Prevote(_) => self.has_voted.can_prevote(),
			grandpa::Message::Precommit(_) => self.has_voted.can_precommit(),
		};

		println!("Sending message {:?}", msg);

		// when locals exist, sign messages on import
		if let (true, &Some((ref pair, ref local_id))) = (should_sign, &self.locals) {
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

			// announce our block hash to peers and propagate the
			// message.
			self.network.announce(self.round, self.set_id, target_hash);
			self.network.send_message(self.round, self.set_id, message.encode(), false);

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

/// A sink for outgoing messages. This signs the messages with the key,
/// if we are an authority. A stream for the signed messages is also returned.
///
/// A future can push unsigned messages into the sink. They will be automatically
/// broadcast to the network. The returned stream should be combined with other input.
pub(crate) fn outgoing_messages<Block: BlockT, N: Network<Block>>(
	round: u64,
	set_id: u64,
	local_key: Option<Arc<ed25519::Pair>>,
	voters: Arc<VoterSet<AuthorityId>>,
	network: N,
	has_voted: HasVoted,
) -> (
	impl Stream<Item=SignedMessage<Block>,Error=Error>,
	OutgoingMessages<Block, N>,
) {
	let locals = local_key.and_then(|pair| {
		let public = pair.public();
		let id = AuthorityId(public.0);
		if voters.contains_key(&id) {
			Some((pair, id))
		} else {
			None
		}
	});

	let (tx, rx) = mpsc::unbounded();
	let outgoing = OutgoingMessages::<Block, N> {
		round,
		set_id,
		network,
		locals,
		sender: tx,
		has_voted,
	};

	let rx = rx.map_err(move |()| Error::Network(
		format!("Failed to receive on unbounded receiver for round {}", round)
	));

	(rx, outgoing)
}

fn check_compact_commit<Block: BlockT>(
	msg: CompactCommit<Block>,
	voters: &VoterSet<AuthorityId>,
) -> Option<CompactCommit<Block>> {
	if msg.precommits.len() != msg.auth_data.len() || msg.precommits.is_empty() {
		debug!(target: "afg", "Skipping malformed compact commit");
		return None;
	}

	// check signatures on all contained precommits.
	for (_, ref id) in &msg.auth_data {
		if !voters.contains_key(id) {
			debug!(target: "afg", "Skipping commit containing unknown voter {}", id);
			return None;
		}
	}

	Some(msg)
}

/// A stream for incoming commit messages. This checks all the signatures on the
/// messages.
pub(crate) fn checked_commit_stream<Block: BlockT, S>(
	inner: S,
	voters: Arc<VoterSet<AuthorityId>>,
)
	-> impl Stream<Item=(u64, CompactCommit<Block>),Error=Error> where
	S: Stream<Item=network_gossip::TopicNotification, Error=()>
{
	inner
		.filter_map(|notification| {
			// this could be optimized by decoding piecewise.
			let decoded = GossipMessage::<Block>::decode(&mut &notification.message[..]);
			if decoded.is_none() {
				trace!(target: "afg", "Skipping malformed commit message {:?}", notification);
			}
			decoded
		})
		.filter_map(move |msg| {
			match msg {
				GossipMessage::Commit(msg) => {
					let round = msg.round;
					let precommits_signed_by: Vec<String> =
						msg.message.auth_data.iter().map(move |(_, a)| {
							format!("{}", a)
						}).collect();
					telemetry!(CONSENSUS_INFO; "afg.received_commit";
						"contains_precommits_signed_by" => ?precommits_signed_by,
						"target_number" => ?msg.message.target_number,
						"target_hash" => ?msg.message.target_hash,
					);
					check_compact_commit::<Block>(msg.message, &*voters).map(move |c| (round.0, c))
				},
				_ => {
					debug!(target: "afg", "Skipping unknown message type");
					return None;
				}
			}
		})
		.map_err(|()| Error::Network(format!("Failed to receive message on unbounded stream")))
}

/// An output sink for commit messages.
pub(crate) struct CommitsOut<Block: BlockT, N: Network<Block>> {
	network: N,
	set_id: SetId,
	is_voter: bool,
	_marker: ::std::marker::PhantomData<Block>,
}

impl<Block: BlockT, N: Network<Block>> CommitsOut<Block, N> {
	/// Create a new commit output stream.
	pub(crate) fn new(network: N, set_id: u64, is_voter: bool) -> Self {
		CommitsOut {
			network,
			set_id: SetId(set_id),
			is_voter,
			_marker: Default::default(),
		}
	}
}

impl<Block: BlockT, N: Network<Block>> Sink for CommitsOut<Block, N> {
	type SinkItem = (u64, Commit<Block>);
	type SinkError = Error;

	fn start_send(&mut self, input: (u64, Commit<Block>)) -> StartSend<Self::SinkItem, Error> {
		if !self.is_voter {
			return Ok(AsyncSink::Ready);
		}

		let (round, commit) = input;
		let round = Round(round);

		telemetry!(CONSENSUS_INFO; "afg.commit_issued";
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

		self.network.send_commit(self.set_id.0, Encode::encode(&message), false);

		Ok(AsyncSink::Ready)
	}

	fn close(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
	fn poll_complete(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
}
