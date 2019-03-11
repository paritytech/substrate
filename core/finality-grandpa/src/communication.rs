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

use std::collections::HashMap;
use std::sync::Arc;

use grandpa::VoterSet;
use futures::prelude::*;
use futures::sync::mpsc;
use log::{debug, trace};
use parity_codec::{Encode, Decode};
use substrate_primitives::{ed25519, Ed25519AuthorityId};
use runtime_primitives::traits::Block as BlockT;
use tokio::timer::Interval;
use crate::{Error, Network, Message, SignedMessage, Commit,
	CompactCommit, GossipMessage, FullCommitMessage, VoteOrPrecommitMessage};

fn localized_payload<E: Encode>(round: u64, set_id: u64, message: &E) -> Vec<u8> {
	(message, round, set_id).encode()
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
struct Round(u64);
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
struct SetId(u64);

enum Broadcast<Block: BlockT> {
	// round, set id, encoded commit.
	Commit(Round, SetId, Vec<u8>),
	// round, set id, encoded signed message.
	Message(Round, SetId, Vec<u8>),
	// round, set id, announcement of block hash that should be downloaded
	Announcement(Round, SetId, Block::Hash),
	// round, set id being dropped.
	DropRound(Round, SetId),
	// set_id being dropped.
	DropSet(SetId),
}

impl<Block: BlockT> Broadcast<Block> {
	fn set_id(&self) -> SetId {
		match *self {
			Broadcast::Commit(_, s, _) => s,
			Broadcast::Message(_, s, _) => s,
			Broadcast::Announcement(_, s, _) => s,
			Broadcast::DropRound(_, s) => s,
			Broadcast::DropSet(s) => s,
		}
	}
}

/// Produces a future that should be run in the background and proxies
/// and rebroadcasts messages.
pub(crate) fn rebroadcasting_network<B: BlockT, N: Network<B>>(network: N) -> (BroadcastWorker<B, N>, BroadcastHandle<B, N>) {
	use std::time::Duration;
	const REBROADCAST_PERIOD: Duration = Duration::from_secs(60);

	let (tx, rx) = mpsc::unbounded();

	(
		BroadcastWorker {
			interval: Interval::new_interval(REBROADCAST_PERIOD),
			set_id: SetId(0), // will be overwritten on first item to broadcast.
			last_commit: None,
			round_messages: (Round(0), Vec::new()),
			announcements: HashMap::new(),
			network: network.clone(),
			incoming_broadcast: rx,
		},
		BroadcastHandle {
			relay: tx,
			network,
		},
	)
}

// A worker which broadcasts messages to the background, potentially
// rebroadcasting.
#[must_use = "network rebroadcast future must be driven to completion"]
pub(crate) struct BroadcastWorker<B: BlockT, N: Network<B>> {
	interval: Interval,
	set_id: SetId,
	last_commit: Option<(Round, Vec<u8>)>,
	round_messages: (Round, Vec<Vec<u8>>),
	announcements: HashMap<B::Hash, Round>,
	network: N,
	incoming_broadcast: mpsc::UnboundedReceiver<Broadcast<B>>,
}

/// A handle used by communication work to broadcast to network.
#[derive(Clone)]
pub(crate) struct BroadcastHandle<B: BlockT, N> {
	relay: mpsc::UnboundedSender<Broadcast<B>>,
	network: N,
}

impl<B: BlockT, N: Network<B>> Future for BroadcastWorker<B, N> {
	type Item = ();
	type Error = Error;

	fn poll(&mut self) -> Poll<(), Error> {
		{
			let mut rebroadcast = false;
			loop {
				match self.interval.poll().map_err(Error::Timer)? {
					Async::NotReady => break,
					Async::Ready(_) => { rebroadcast = true; }
				}
			}

			if rebroadcast {
				let SetId(set_id) = self.set_id;
				if let Some((Round(c_round), ref c_commit)) = self.last_commit {
					self.network.send_commit(c_round, set_id, c_commit.clone());
				}

				let Round(round) = self.round_messages.0;
				for message in self.round_messages.1.iter().cloned() {
					self.network.send_message(round, set_id, message);
				}

				for (&announce_hash, &Round(round)) in &self.announcements {
					self.network.announce(round, set_id, announce_hash);
				}
			}
		}
		loop {
			match self.incoming_broadcast.poll().expect("UnboundedReceiver does not yield errors; qed") {
				Async::NotReady => return Ok(Async::NotReady),
				Async::Ready(None) => return Err(Error::Network(
					"all broadcast handles dropped, connection to network severed".into()
				)),
				Async::Ready(Some(item)) => {
					if item.set_id() > self.set_id {
						self.set_id = item.set_id();
						self.last_commit = None;
						self.round_messages = (Round(0), Vec::new());
						self.announcements.clear();
					}

					match item {
						Broadcast::Commit(round, set_id, commit) => {
							if self.set_id == set_id {
								if round >= self.last_commit.as_ref()
									.map_or(Round(0), |&(r, _)| r)
								{
									self.last_commit = Some((round, commit.clone()));
								}
							}

							// always send out to network.
							self.network.send_commit(round.0, self.set_id.0, commit);
						}
						Broadcast::Message(round, set_id, message) => {
							if self.set_id == set_id {
								if round > self.round_messages.0 {
									self.round_messages = (round, vec![message.clone()]);
								} else if round == self.round_messages.0 {
									self.round_messages.1.push(message.clone());
								};

								// ignore messages from earlier rounds.
							}

							// always send out to network.
							self.network.send_message(round.0, set_id.0, message);
						}
						Broadcast::Announcement(round, set_id, hash) => {
							if self.set_id == set_id {
								self.announcements.insert(hash, round);
							}

							// always send out.
							self.network.announce(round.0, set_id.0, hash);
						}
						Broadcast::DropRound(round, set_id) => {
							// stop making announcements for any dead rounds.
							self.announcements.retain(|_, &mut r| r > round);
							self.network.drop_round_messages(round.0, set_id.0);
						}
						Broadcast::DropSet(set_id) => {
							// stop making announcements for any dead rounds.
							self.network.drop_set_messages(set_id.0);
						}
					}
				}
			}
		}
	}
}

impl<B: BlockT, N: Network<B>> Network<B> for BroadcastHandle<B, N> {
	type In = N::In;

	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		self.network.messages_for(round, set_id)
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let _ = self.relay.unbounded_send(Broadcast::Message(Round(round), SetId(set_id), message));
	}

	fn drop_round_messages(&self, round: u64, set_id: u64) {
		let _ = self.relay.unbounded_send(Broadcast::DropRound(Round(round), SetId(set_id)));
	}

	fn drop_set_messages(&self, set_id: u64) {
		let _ = self.relay.unbounded_send(Broadcast::DropSet(SetId(set_id)));
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		self.network.commit_messages(set_id)
	}

	fn send_commit(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let _ = self.relay.unbounded_send(Broadcast::Commit(Round(round), SetId(set_id), message));
	}

	fn announce(&self, round: u64, set_id: u64, block: B::Hash) {
		let _ = self.relay.unbounded_send(
			Broadcast::Announcement(Round(round), SetId(set_id), block)
		);
	}
}

// check a message.
pub(crate) fn check_message_sig<Block: BlockT>(
	message: &Message<Block>,
	id: &Ed25519AuthorityId,
	signature: &ed25519::Signature,
	round: u64,
	set_id: u64,
) -> Result<(), ()> {
	let as_public = ed25519::Public::from_raw(id.0);
	let encoded_raw = localized_payload(round, set_id, message);
	if ed25519::verify_strong(signature, &encoded_raw, as_public) {
		Ok(())
	} else {
		debug!(target: "afg", "Bad signature on message from {:?}", id);
		Err(())
	}
}

/// converts a message stream into a stream of signed messages.
/// the output stream checks signatures also.
pub(crate) fn checked_message_stream<Block: BlockT, S>(
	inner: S,
	voters: Arc<VoterSet<Ed25519AuthorityId>>,
)
	-> impl Stream<Item=SignedMessage<Block>,Error=Error> where
	S: Stream<Item=Vec<u8>,Error=()>
{
	inner
		.filter_map(|raw| {
			let decoded = GossipMessage::<Block>::decode(&mut &raw[..]);
			if decoded.is_none() {
				debug!(target: "afg", "Skipping malformed message {:?}", raw);
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

pub(crate) struct OutgoingMessages<Block: BlockT, N: Network<Block>> {
	round: u64,
	set_id: u64,
	locals: Option<(Arc<ed25519::Pair>, Ed25519AuthorityId)>,
	sender: mpsc::UnboundedSender<SignedMessage<Block>>,
	network: N,
}

impl<Block: BlockT, N: Network<Block>> Sink for OutgoingMessages<Block, N>
{
	type SinkItem = Message<Block>;
	type SinkError = Error;

	fn start_send(&mut self, msg: Message<Block>) -> StartSend<Message<Block>, Error> {
		// when locals exist, sign messages on import
		if let Some((ref pair, local_id)) = self.locals {
			let encoded = localized_payload(self.round, self.set_id, &msg);
			let signature = pair.sign(&encoded[..]);

			let target_hash = msg.target().0.clone();
			let signed = SignedMessage::<Block> {
				message: msg,
				signature,
				id: local_id,
			};

			let message = GossipMessage::VoteOrPrecommit(VoteOrPrecommitMessage::<Block> {
				message: signed.clone(),
				round: self.round,
				set_id: self.set_id,
			});

			// announce our block hash to peers and propagate the
			// message.
			self.network.announce(self.round, self.set_id, target_hash);
			self.network.send_message(self.round, self.set_id, message.encode());

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

impl<Block: BlockT, N: Network<Block>> Drop for OutgoingMessages<Block, N> {
	fn drop(&mut self) {
		self.network.drop_round_messages(self.round, self.set_id);
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
	voters: Arc<VoterSet<Ed25519AuthorityId>>,
	network: N,
) -> (
	impl Stream<Item=SignedMessage<Block>,Error=Error>,
	OutgoingMessages<Block, N>,
) {
	let locals = local_key.and_then(|pair| {
		let public = pair.public();
		let id = Ed25519AuthorityId(public.0);
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
	};

	let rx = rx.map_err(move |()| Error::Network(
		format!("Failed to receive on unbounded receiver for round {}", round)
	));

	(rx, outgoing)
}

fn check_compact_commit<Block: BlockT>(
	msg: CompactCommit<Block>,
	voters: &VoterSet<Ed25519AuthorityId>,
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
	voters: Arc<VoterSet<Ed25519AuthorityId>>,
)
	-> impl Stream<Item=(u64, CompactCommit<Block>),Error=Error> where
	S: Stream<Item=Vec<u8>,Error=()>
{
	inner
		.filter_map(|raw| {
			// this could be optimized by decoding piecewise.
			let decoded = GossipMessage::<Block>::decode(&mut &raw[..]);
			if decoded.is_none() {
				trace!(target: "afg", "Skipping malformed commit message {:?}", raw);
			}
			decoded
		})
		.filter_map(move |msg| {
			match msg {
				GossipMessage::Commit(msg) => {
					let round = msg.round;
					check_compact_commit::<Block>(msg.message, &*voters).map(move |c| (round, c))
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
	set_id: u64,
	_marker: ::std::marker::PhantomData<Block>,
	is_voter: bool,
}

impl<Block: BlockT, N: Network<Block>> CommitsOut<Block, N> {
	/// Create a new commit output stream.
	pub(crate) fn new(network: N, set_id: u64, is_voter: bool) -> Self {
		CommitsOut {
			network,
			set_id,
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

		self.network.send_commit(round, self.set_id, Encode::encode(&message));

		Ok(AsyncSink::Ready)
	}

	fn close(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
	fn poll_complete(&mut self) -> Poll<(), Error> { Ok(Async::Ready(())) }
}

impl<Block: BlockT, N: Network<Block>> Drop for CommitsOut<Block, N> {
	fn drop(&mut self) {
		self.network.drop_set_messages(self.set_id);
	}
}
