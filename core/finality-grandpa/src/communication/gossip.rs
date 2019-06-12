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

//! Gossip and politeness for polite-grandpa.
//!
//! This module implements the following message types:
//! #### Neighbor Packet
//!
//! The neighbor packet is sent to only our neighbors. It contains this information
//!
//!   - Current Round
//!   - Current voter set ID
//!   - Last finalized hash from commit messages.
//!
//! If a peer is at a given voter set, it is impolite to send messages from
//! an earlier voter set. It is extremely impolite to send messages
//! from a future voter set. "future-set" messages can be dropped and ignored.
//!
//! If a peer is at round r, is impolite to send messages about r-2 or earlier and extremely
//! impolite to send messages about r+1 or later. "future-round" messages can
//!  be dropped and ignored.
//!
//! It is impolite to send a neighbor packet which moves backwards in protocol state.
//!
//! This is beneficial if it conveys some progress in the protocol state of the peer.
//!
//! #### Prevote / Precommit
//!
//! These are votes within a round. Noting that we receive these messages
//! from our peers who are not necessarily voters, we have to account the benefit
//! based on what they might have seen.
//!
//! #### Propose
//!
//! This is a broadcast by a known voter of the last-round estimate.

//! #### Commit
//!
//! These are used to announce past agreement of finality.
//!
//! It is impolite to send commits which are earlier than the last commit
//! sent. It is especially impolite to send commits which are invalid, or from
//! a different Set ID than the receiving peer has indicated.
//!
//! Sending a commit is polite when it may finalize something that the receiving peer
//! was not aware of.
//!
//! ## Expiration
//!
//! We keep some amount of recent rounds' messages, but do not accept new ones from rounds
//! older than our current_round - 1.
//!
//! ## Message Validation
//!
//! We only send polite messages to peers,

use runtime_primitives::traits::{NumberFor, Block as BlockT, Zero};
use network::consensus_gossip::{self as network_gossip, MessageIntent, ValidatorContext};
use network::{config::Roles, PeerId};
use parity_codec::{Encode, Decode};
use crate::ed25519::Public as AuthorityId;

use substrate_telemetry::{telemetry, CONSENSUS_DEBUG};
use log::{trace, debug, warn};
use futures::prelude::*;
use futures::sync::mpsc;

use crate::{CompactCommit, SignedMessage};
use super::{cost, benefit, Round, SetId};

use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

const REBROADCAST_AFTER: Duration = Duration::from_secs(60 * 5);

/// An outcome of examining a message.
#[derive(Debug, PartialEq, Clone, Copy)]
enum Consider {
	/// Accept the message.
	Accept,
	/// Message is too early. Reject.
	RejectPast,
	/// Message is from the future. Reject.
	RejectFuture,
	/// Message cannot be evaluated. Reject.
	RejectOutOfScope,
}

/// A view of protocol state.
#[derive(Debug)]
struct View<N> {
	round: Round, // the current round we are at.
	set_id: SetId, // the current voter set id.
	last_commit: Option<N>, // commit-finalized block height, if any.
}

impl<N> Default for View<N> {
	fn default() -> Self {
		View {
			round: Round(0),
			set_id: SetId(0),
			last_commit: None,
		}
	}
}

impl<N: Ord> View<N> {
	/// Update the set ID. implies a reset to round 0.
	fn update_set(&mut self, set_id: SetId) {
		if set_id != self.set_id {
			self.set_id = set_id;
			self.round = Round(0);
		}
	}

	/// Consider a round and set ID combination under a current view.
	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		// only from current set
		if set_id < self.set_id { return Consider::RejectPast }
		if set_id > self.set_id { return Consider::RejectFuture }

		// only r-1 ... r+1
		if round.0 > self.round.0.saturating_add(1) { return Consider::RejectFuture }
		if round.0 < self.round.0.saturating_sub(1) { return Consider::RejectPast }

		Consider::Accept
	}

	/// Consider a set-id global message. Rounds are not taken into account, but are implicitly
	/// because we gate on finalization of a further block than a previous commit.
	fn consider_global(&self, set_id: SetId, number: N) -> Consider {
		// only from current set
		if set_id < self.set_id { return Consider::RejectPast }
		if set_id > self.set_id { return Consider::RejectFuture }

		// only commits which claim to prove a higher block number than
		// the one we're aware of.
		match self.last_commit {
			None => Consider::Accept,
			Some(ref num) => if num < &number {
				Consider::Accept
			} else {
				Consider::RejectPast
			}
		}
	}
}

const KEEP_RECENT_ROUNDS: usize = 3;

/// Tracks topics we keep messages for.
struct KeepTopics<B: BlockT> {
	current_set: SetId,
	rounds: VecDeque<(Round, SetId)>,
	reverse_map: HashMap<B::Hash, (Option<Round>, SetId)>
}

impl<B: BlockT> KeepTopics<B> {
	fn new() -> Self {
		KeepTopics {
			current_set: SetId(0),
			rounds: VecDeque::with_capacity(KEEP_RECENT_ROUNDS + 1),
			reverse_map: HashMap::new(),
		}
	}

	fn push(&mut self, round: Round, set_id: SetId) {
		self.current_set = std::cmp::max(self.current_set, set_id);
		self.rounds.push_back((round, set_id));

		// the 1 is for the current round.
		while self.rounds.len() > KEEP_RECENT_ROUNDS + 1 {
			let _ = self.rounds.pop_front();
		}

		let mut map = HashMap::with_capacity(KEEP_RECENT_ROUNDS + 2);
		map.insert(super::global_topic::<B>(self.current_set.0), (None, self.current_set));

		for &(round, set) in &self.rounds {
			map.insert(
				super::round_topic::<B>(round.0, set.0),
				(Some(round), set)
			);
		}

		self.reverse_map = map;
	}

	fn topic_info(&self, topic: &B::Hash) -> Option<(Option<Round>, SetId)> {
		self.reverse_map.get(topic).cloned()
	}
}

// topics to send to a neighbor based on their view.
fn neighbor_topics<B: BlockT>(view: &View<NumberFor<B>>) -> Vec<B::Hash> {
	let s = view.set_id;
	let mut topics = vec![
		super::global_topic::<B>(s.0),
		super::round_topic::<B>(view.round.0, s.0),
	];

	if view.round.0 != 0 {
		let r = Round(view.round.0 - 1);
		topics.push(super::round_topic::<B>(r.0, s.0))
	}

	topics
}

/// Grandpa gossip message type.
/// This is the root type that gets encoded and sent on the network.
#[derive(Debug, Encode, Decode)]
pub(super) enum GossipMessage<Block: BlockT> {
	/// Grandpa message with round and set info.
	VoteOrPrecommit(VoteOrPrecommitMessage<Block>),
	/// Grandpa commit message with round and set info.
	Commit(FullCommitMessage<Block>),
	/// A neighbor packet. Not repropagated.
	Neighbor(VersionedNeighborPacket<NumberFor<Block>>),
}

impl<Block: BlockT> From<NeighborPacket<NumberFor<Block>>> for GossipMessage<Block> {
	fn from(neighbor: NeighborPacket<NumberFor<Block>>) -> Self {
		GossipMessage::Neighbor(VersionedNeighborPacket::V1(neighbor))
	}
}

/// Network level message with topic information.
#[derive(Debug, Encode, Decode)]
pub(super) struct VoteOrPrecommitMessage<Block: BlockT> {
	/// The round this message is from.
	pub(super) round: Round,
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
	/// The message itself.
	pub(super) message: SignedMessage<Block>,
}

/// Network level commit message with topic information.
#[derive(Debug, Encode, Decode)]
pub(super) struct FullCommitMessage<Block: BlockT> {
	/// The round this message is from.
	pub(super) round: Round,
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
	/// The compact commit message.
	pub(super) message: CompactCommit<Block>,
}

/// V1 neighbor packet. Neighbor packets are sent from nodes to their peers
/// and are not repropagated. These contain information about the node's state.
#[derive(Debug, Encode, Decode, Clone)]
pub(super) struct NeighborPacket<N> {
	round: Round,
	set_id: SetId,
	commit_finalized_height: N,
}

/// A versioned neighbor packet.
#[derive(Debug, Encode, Decode)]
pub(super) enum VersionedNeighborPacket<N> {
	#[codec(index = "1")]
	V1(NeighborPacket<N>),
}

impl<N> VersionedNeighborPacket<N> {
	fn into_neighbor_packet(self) -> NeighborPacket<N> {
		match self {
			VersionedNeighborPacket::V1(p) => p,
		}
	}
}

/// Misbehavior that peers can perform.
///
/// `cost` gives a cost that can be used to perform cost/benefit analysis of a
/// peer.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum Misbehavior {
	// invalid neighbor message, considering the last one.
	InvalidViewChange,
	// could not decode neighbor message. bytes-length of the packet.
	UndecodablePacket(i32),
	// Bad commit message
	BadCommitMessage {
		signatures_checked: i32,
		blocks_loaded: i32,
		equivocations_caught: i32,
	},
	// A message received that's from the future relative to our view.
	// always misbehavior.
	FutureMessage,
	// A message received that cannot be evaluated relative to our view.
	// This happens before we have a view and have sent out neighbor packets.
	// always misbehavior.
	OutOfScopeMessage,
}

impl Misbehavior {
	pub(super) fn cost(&self) -> i32 {
		use Misbehavior::*;

		match *self {
			InvalidViewChange => cost::INVALID_VIEW_CHANGE,
			UndecodablePacket(bytes) =>  bytes.saturating_mul(cost::PER_UNDECODABLE_BYTE),
			BadCommitMessage { signatures_checked, blocks_loaded, equivocations_caught } => {
				let cost = cost::PER_SIGNATURE_CHECKED
					.saturating_mul(signatures_checked)
					.saturating_add(cost::PER_BLOCK_LOADED.saturating_mul(blocks_loaded));

				let benefit = equivocations_caught.saturating_mul(benefit::PER_EQUIVOCATION);

				(benefit as i32).saturating_add(cost as i32)
			},
			FutureMessage => cost::FUTURE_MESSAGE,
			OutOfScopeMessage => cost::OUT_OF_SCOPE_MESSAGE,
		}
	}
}

struct PeerInfo<N> {
	view: View<N>,
}

impl<N> PeerInfo<N> {
	fn new() -> Self {
		PeerInfo {
			view: View::default(),
		}
	}
}

/// The peers we're connected do in gossip.
struct Peers<N> {
	inner: HashMap<PeerId, PeerInfo<N>>,
}

impl<N> Default for Peers<N> {
	fn default() -> Self {
		Peers { inner: HashMap::new() }
	}
}

impl<N: Ord> Peers<N> {
	fn new_peer(&mut self, who: PeerId) {
		self.inner.insert(who, PeerInfo::new());
	}

	fn peer_disconnected(&mut self, who: &PeerId) {
		self.inner.remove(who);
	}

	// returns a reference to the new view, if the peer is known.
	fn update_peer_state(&mut self, who: &PeerId, update: NeighborPacket<N>)
		-> Result<Option<&View<N>>, Misbehavior>
	{
		let peer = match self.inner.get_mut(who) {
			None => return Ok(None),
			Some(p) => p,
		};

		let invalid_change = peer.view.set_id > update.set_id
			|| peer.view.round > update.round && peer.view.set_id == update.set_id
			|| peer.view.last_commit.as_ref() > Some(&update.commit_finalized_height);

		if invalid_change {
			return Err(Misbehavior::InvalidViewChange);
		}

		peer.view = View {
			round: update.round,
			set_id: update.set_id,
			last_commit: Some(update.commit_finalized_height),
		};

		trace!(target: "afg", "Peer {} updated view. Now at {:?}, {:?}",
			who, peer.view.round, peer.view.set_id);

		Ok(Some(&peer.view))
	}

	fn update_commit_height(&mut self, who: &PeerId, new_height: N) -> Result<(), Misbehavior> {
		let peer = match self.inner.get_mut(who) {
			None => return Ok(()),
			Some(p) => p,
		};

		// this doesn't allow a peer to send us unlimited commits with the
		// same height, because there is still a misbehavior condition based on
		// sending commits that are <= the best we are aware of.
		if peer.view.last_commit.as_ref() > Some(&new_height) {
			return Err(Misbehavior::InvalidViewChange);
		}

		peer.view.last_commit = Some(new_height);

		Ok(())
	}

	fn peer<'a>(&'a self, who: &PeerId) -> Option<&'a PeerInfo<N>> {
		self.inner.get(who)
	}
}

#[derive(Debug, PartialEq)]
pub(super) enum Action<H>  {
	// repropagate under given topic, to the given peers, applying cost/benefit to originator.
	Keep(H, i32),
	// discard and process.
	ProcessAndDiscard(H, i32),
	// discard, applying cost/benefit to originator.
	Discard(i32),
}

struct Inner<Block: BlockT> {
	local_view: Option<View<NumberFor<Block>>>,
	peers: Peers<NumberFor<Block>>,
	live_topics: KeepTopics<Block>,
	authorities: Vec<AuthorityId>,
	config: crate::Config,
	next_rebroadcast: Instant,
}

type MaybeMessage<Block> = Option<(Vec<PeerId>, NeighborPacket<NumberFor<Block>>)>;

impl<Block: BlockT> Inner<Block> {
	fn new(config: crate::Config) -> Self {
		Inner {
			local_view: None,
			peers: Peers::default(),
			live_topics: KeepTopics::new(),
			next_rebroadcast: Instant::now() + REBROADCAST_AFTER,
			authorities: Vec::new(),
			config,
		}
	}

	/// Note a round in the current set has started.
	fn note_round(&mut self, round: Round) -> MaybeMessage<Block> {
		{
			let local_view = match self.local_view {
				None => return None,
				Some(ref mut v) => if v.round == round {
					return None
				} else {
					v
				},
			};

			let set_id = local_view.set_id;

			debug!(target: "afg", "Voter {} noting beginning of round {:?} to network.",
				self.config.name(), (round,set_id));

			local_view.round = round;

			self.live_topics.push(round, set_id);
		}
		self.multicast_neighbor_packet()
	}

	/// Note that a voter set with given ID has started. Does nothing if the last
	/// call to the function was with the same `set_id`.
	fn note_set(&mut self, set_id: SetId, authorities: Vec<AuthorityId>) -> MaybeMessage<Block> {
		{
			let local_view = match self.local_view {
				ref mut x @ None => x.get_or_insert(View {
					round: Round(0),
					set_id,
					last_commit: None,
				}),
				Some(ref mut v) => if v.set_id == set_id {
					return None
				} else {
					v
				},
			};

			local_view.update_set(set_id);
			self.live_topics.push(Round(0), set_id);
			self.authorities = authorities;
		}
		self.multicast_neighbor_packet()
	}

	/// Note that we've imported a commit finalizing a given block.
	fn note_commit_finalized(&mut self, finalized: NumberFor<Block>) -> MaybeMessage<Block> {
		{
			match self.local_view {
				None => return None,
				Some(ref mut v) => if v.last_commit.as_ref() < Some(&finalized) {
					v.last_commit = Some(finalized);
				} else {
					return None
				},
			};
		}

		self.multicast_neighbor_packet()
	}

	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		self.local_view.as_ref().map(|v| v.consider_vote(round, set_id))
			.unwrap_or(Consider::RejectOutOfScope)
	}

	fn consider_global(&self, set_id: SetId, number: NumberFor<Block>) -> Consider {
		self.local_view.as_ref().map(|v| v.consider_global(set_id, number))
			.unwrap_or(Consider::RejectOutOfScope)
	}

	fn cost_past_rejection(&self, _who: &PeerId, _round: Round, _set_id: SetId) -> i32 {
		// hardcoded for now.
		cost::PAST_REJECTION
	}

	fn validate_round_message(&self, who: &PeerId, full: &VoteOrPrecommitMessage<Block>)
		-> Action<Block::Hash>
	{
		match self.consider_vote(full.round, full.set_id) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectOutOfScope => return Action::Discard(Misbehavior::OutOfScopeMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::Accept => {},
		}

		// ensure authority is part of the set.
		if !self.authorities.contains(&full.message.id) {
			telemetry!(CONSENSUS_DEBUG; "afg.bad_msg_signature"; "signature" => ?full.message.id);
			return Action::Discard(cost::UNKNOWN_VOTER);
		}

		if let Err(()) = super::check_message_sig::<Block>(
			&full.message.message,
			&full.message.id,
			&full.message.signature,
			full.round.0,
			full.set_id.0,
		) {
			debug!(target: "afg", "Bad message signature {}", full.message.id);
			telemetry!(CONSENSUS_DEBUG; "afg.bad_msg_signature"; "signature" => ?full.message.id);
			return Action::Discard(cost::BAD_SIGNATURE);
		}

		let topic = super::round_topic::<Block>(full.round.0, full.set_id.0);
		Action::Keep(topic, benefit::ROUND_MESSAGE)
	}

	fn validate_commit_message(&mut self, who: &PeerId, full: &FullCommitMessage<Block>)
		-> Action<Block::Hash>
	{

		if let Err(misbehavior) = self.peers.update_commit_height(who, full.message.target_number) {
			return Action::Discard(misbehavior.cost());
		}

		match self.consider_global(full.set_id, full.message.target_number) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::RejectOutOfScope => return Action::Discard(Misbehavior::OutOfScopeMessage.cost()),
			Consider::Accept => {},

		}

		if full.message.precommits.len() != full.message.auth_data.len() || full.message.precommits.is_empty() {
			debug!(target: "afg", "Malformed compact commit");
			telemetry!(CONSENSUS_DEBUG; "afg.malformed_compact_commit";
				"precommits_len" => ?full.message.precommits.len(),
				"auth_data_len" => ?full.message.auth_data.len(),
				"precommits_is_empty" => ?full.message.precommits.is_empty(),
			);
			return Action::Discard(cost::MALFORMED_COMMIT);
		}

		// always discard commits initially and rebroadcast after doing full
		// checking.
		let topic = super::global_topic::<Block>(full.set_id.0);
		Action::ProcessAndDiscard(topic, benefit::BASIC_VALIDATED_COMMIT)
	}

	fn import_neighbor_message(&mut self, who: &PeerId, update: NeighborPacket<NumberFor<Block>>)
		-> (Vec<Block::Hash>, Action<Block::Hash>)
	{
		let (cb, topics) = match self.peers.update_peer_state(who, update) {
			Ok(view) => (100i32, view.map(|view| neighbor_topics::<Block>(view))),
			Err(misbehavior) => (misbehavior.cost(), None)
		};

		let neighbor_topics = topics.unwrap_or_default();

		// always discard, it's valid for one hop.
		(neighbor_topics, Action::Discard(cb))
	}

	fn multicast_neighbor_packet(&self) -> MaybeMessage<Block> {
		self.local_view.as_ref().map(|local_view| {
			let packet = NeighborPacket {
				round: local_view.round,
				set_id: local_view.set_id,
				commit_finalized_height: local_view.last_commit.unwrap_or(Zero::zero()),
			};

			let peers = self.peers.inner.keys().cloned().collect();
			(peers, packet)
		})
	}
}

/// A validator for GRANDPA gossip messages.
pub(super) struct GossipValidator<Block: BlockT> {
	inner: parking_lot::RwLock<Inner<Block>>,
	report_sender: mpsc::UnboundedSender<PeerReport>,
}

impl<Block: BlockT> GossipValidator<Block> {
	/// Create a new gossip-validator. This initialized the current set to 0.
	pub(super) fn new(config: crate::Config) -> (GossipValidator<Block>, ReportStream) {
		let (tx, rx) = mpsc::unbounded();
		let val = GossipValidator {
			inner: parking_lot::RwLock::new(Inner::new(config)),
			report_sender: tx,
		};

		(val, ReportStream { reports: rx })
	}

	/// Note a round in the current set has started.
	pub(super) fn note_round<F>(&self, round: Round, send_neighbor: F)
		where F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>)
	{
		let maybe_msg = self.inner.write().note_round(round);
		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	/// Note that a voter set with given ID has started. Updates the current set to given
	/// value and initializes the round to 0.
	pub(super) fn note_set<F>(&self, set_id: SetId, authorities: Vec<AuthorityId>, send_neighbor: F)
		where F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>)
	{
		let maybe_msg = self.inner.write().note_set(set_id, authorities);
		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	/// Note that we've imported a commit finalizing a given block.
	pub(super) fn note_commit_finalized<F>(&self, finalized: NumberFor<Block>, send_neighbor: F)
		where F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>)
	{
		let maybe_msg = self.inner.write().note_commit_finalized(finalized);
		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	fn report(&self, who: PeerId, cost_benefit: i32) {
		let _ = self.report_sender.unbounded_send(PeerReport { who, cost_benefit });
	}

	pub(super) fn do_validate(&self, who: &PeerId, mut data: &[u8])
		-> (Action<Block::Hash>, Vec<Block::Hash>)
	{
		let mut broadcast_topics = Vec::new();
		let action = {
			match GossipMessage::<Block>::decode(&mut data) {
				Some(GossipMessage::VoteOrPrecommit(ref message))
					=> self.inner.write().validate_round_message(who, message),
				Some(GossipMessage::Commit(ref message)) => self.inner.write().validate_commit_message(who, message),
				Some(GossipMessage::Neighbor(update)) => {
					let (topics, action) = self.inner.write().import_neighbor_message(
						who,
						update.into_neighbor_packet(),
					);

					broadcast_topics = topics;
					action
				}
				None => {
					debug!(target: "afg", "Error decoding message");
					telemetry!(CONSENSUS_DEBUG; "afg.err_decoding_msg"; "" => "");

					let len = std::cmp::min(i32::max_value() as usize, data.len()) as i32;
					Action::Discard(Misbehavior::UndecodablePacket(len).cost())
				}
			}
		};

		(action, broadcast_topics)
	}
}

impl<Block: BlockT> network_gossip::Validator<Block> for GossipValidator<Block> {
	fn new_peer(&self, context: &mut dyn ValidatorContext<Block>, who: &PeerId, _roles: Roles) {
		let packet = {
			let mut inner = self.inner.write();
			inner.peers.new_peer(who.clone());

			inner.local_view.as_ref().map(|v| {
				NeighborPacket {
					round: v.round,
					set_id: v.set_id,
					commit_finalized_height: v.last_commit.unwrap_or(Zero::zero()),
				}
			})
		};

		if let Some(packet) = packet {
			let packet_data = GossipMessage::<Block>::from(packet).encode();
			context.send_message(who, packet_data);
		}
	}

	fn peer_disconnected(&self, _context: &mut dyn ValidatorContext<Block>, who: &PeerId) {
		self.inner.write().peers.peer_disconnected(who);
	}

	fn validate(&self, context: &mut dyn ValidatorContext<Block>, who: &PeerId, data: &[u8])
		-> network_gossip::ValidationResult<Block::Hash>
	{
		let (action, broadcast_topics) = self.do_validate(who, data);

		// not with lock held!
		for topic in broadcast_topics {
			context.send_topic(who, topic, false);
		}

		match action {
			Action::Keep(topic, cb) => {
				self.report(who.clone(), cb);
				context.broadcast_message(topic, data.to_vec(), false);
				network_gossip::ValidationResult::ProcessAndKeep(topic)
			}
			Action::ProcessAndDiscard(topic, cb) => {
				self.report(who.clone(), cb);
				network_gossip::ValidationResult::ProcessAndDiscard(topic)
			}
			Action::Discard(cb) => {
				self.report(who.clone(), cb);
				network_gossip::ValidationResult::Discard
			}
		}
	}

	fn message_allowed<'a>(&'a self)
		-> Box<dyn FnMut(&PeerId, MessageIntent, &Block::Hash, &[u8]) -> bool + 'a>
	{
		let (inner, do_rebroadcast) = {
			use parking_lot::RwLockWriteGuard;

			let mut inner = self.inner.write();
			let now = Instant::now();
			let do_rebroadcast = if now >= inner.next_rebroadcast {
				inner.next_rebroadcast = now + REBROADCAST_AFTER;
				true
			} else {
				false
			};

			// downgrade to read-lock.
			(RwLockWriteGuard::downgrade(inner), do_rebroadcast)
		};

		Box::new(move |who, intent, topic, mut data| {
			if let MessageIntent::PeriodicRebroadcast = intent {
				return do_rebroadcast;
			}

			let peer = match inner.peers.peer(who) {
				None => return false,
				Some(x) => x,
			};

			// if the topic is not something we're keeping at the moment,
			// do not send.
			let (maybe_round, set_id) = match inner.live_topics.topic_info(&topic) {
				None => return false,
				Some(x) => x,
			};

			// if the topic is not something the peer accepts, discard.
			if let Some(round) = maybe_round {
				return peer.view.consider_vote(round, set_id) == Consider::Accept
			}

			// global message.
			let local_view = match inner.local_view {
				Some(ref v) => v,
				None => return false, // cannot evaluate until we have a local view.
			};

			let our_best_commit = local_view.last_commit;
			let peer_best_commit = peer.view.last_commit;

			match GossipMessage::<Block>::decode(&mut data) {
				None => false,
				Some(GossipMessage::Commit(full)) => {
					// we only broadcast our best commit and only if it's
					// better than last received by peer.
					Some(full.message.target_number) == our_best_commit
					&& Some(full.message.target_number) > peer_best_commit
				}
				Some(GossipMessage::Neighbor(_)) => false,
				Some(GossipMessage::VoteOrPrecommit(_)) => false, // should not be the case.
			}
		})
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(Block::Hash, &[u8]) -> bool + 'a> {
		let inner = self.inner.read();
		Box::new(move |topic, mut data| {
			// if the topic is not one of the ones that we are keeping at the moment,
			// it is expired.
			match inner.live_topics.topic_info(&topic) {
				None => return true,
				Some((Some(_), _)) => return false, // round messages don't require further checking.
				Some((None, _)) => {},
			};

			let local_view = match inner.local_view {
				Some(ref v) => v,
				None => return true, // no local view means we can't evaluate or hold any topic.
			};

			// global messages -- only keep the best commit.
			let best_commit = local_view.last_commit;

			match GossipMessage::<Block>::decode(&mut data) {
				None => true,
				Some(GossipMessage::Commit(full))
					=> Some(full.message.target_number) != best_commit,
				Some(_) => true,
			}
		})
	}
}

struct PeerReport {
	who: PeerId,
	cost_benefit: i32,
}

// wrapper around a stream of reports.
#[must_use = "The report stream must be consumed"]
pub(super) struct ReportStream {
	reports: mpsc::UnboundedReceiver<PeerReport>,
}

impl ReportStream {
	/// Consume the report stream, converting it into a future that
	/// handles all reports.
	pub(super) fn consume<B, N>(self, net: N)
		-> impl Future<Item=(),Error=()> + Send + 'static
	where
		B: BlockT,
		N: super::Network<B> + Send + 'static,
	{
		ReportingTask {
			reports: self.reports,
			net,
			_marker: Default::default(),
		}
	}
}

/// A future for reporting peers.
#[must_use = "Futures do nothing unless polled"]
struct ReportingTask<B, N> {
	reports: mpsc::UnboundedReceiver<PeerReport>,
	net: N,
	_marker: std::marker::PhantomData<B>,
}

impl<B: BlockT, N: super::Network<B>> Future for ReportingTask<B, N> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<(), ()> {
		loop {
			match self.reports.poll() {
				Err(_) => {
					warn!(target: "afg", "Report stream terminated unexpectedly");
					return Ok(Async::Ready(()))
				}
				Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
				Ok(Async::Ready(Some(PeerReport { who, cost_benefit }))) =>
					self.net.report(who, cost_benefit),
				Ok(Async::NotReady) => return Ok(Async::NotReady),
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use network_gossip::Validator as GossipValidatorT;
	use network::test::Block;

	// some random config (not really needed)
	fn config() -> crate::Config {
		crate::Config {
			gossip_duration: Duration::from_millis(10),
			justification_period: 256,
			local_key: None,
			name: None,
		}
	}

	#[test]
	fn view_vote_rules() {
		let view = View { round: Round(100), set_id: SetId(1), last_commit: Some(1000u64) };

		assert_eq!(view.consider_vote(Round(98), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_vote(Round(1), SetId(0)), Consider::RejectPast);
		assert_eq!(view.consider_vote(Round(1000), SetId(0)), Consider::RejectPast);

		assert_eq!(view.consider_vote(Round(99), SetId(1)), Consider::Accept);
		assert_eq!(view.consider_vote(Round(100), SetId(1)), Consider::Accept);
		assert_eq!(view.consider_vote(Round(101), SetId(1)), Consider::Accept);

		assert_eq!(view.consider_vote(Round(102), SetId(1)), Consider::RejectFuture);
		assert_eq!(view.consider_vote(Round(1), SetId(2)), Consider::RejectFuture);
		assert_eq!(view.consider_vote(Round(1000), SetId(2)), Consider::RejectFuture);
	}

	#[test]
	fn view_global_message_rules() {
		let view = View { round: Round(100), set_id: SetId(2), last_commit: Some(1000u64) };

		assert_eq!(view.consider_global(SetId(3), 1), Consider::RejectFuture);
		assert_eq!(view.consider_global(SetId(3), 1000), Consider::RejectFuture);
		assert_eq!(view.consider_global(SetId(3), 10000), Consider::RejectFuture);

		assert_eq!(view.consider_global(SetId(1), 1), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(1), 1000), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(1), 10000), Consider::RejectPast);

		assert_eq!(view.consider_global(SetId(2), 1), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(2), 1000), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(2), 1001), Consider::Accept);
		assert_eq!(view.consider_global(SetId(2), 10000), Consider::Accept);
	}

	#[test]
	fn unknown_peer_cannot_be_updated() {
		let mut peers = Peers::default();
		let id = PeerId::random();

		let update = NeighborPacket {
			round: Round(5),
			set_id: SetId(10),
			commit_finalized_height: 50,
		};

		let res = peers.update_peer_state(&id, update.clone());
		assert!(res.unwrap().is_none());

		// connect & disconnect.
		peers.new_peer(id.clone());
		peers.peer_disconnected(&id);

		let res = peers.update_peer_state(&id, update.clone());
		assert!(res.unwrap().is_none());
	}

	#[test]
	fn update_peer_state() {
		let update1 = NeighborPacket {
			round: Round(5),
			set_id: SetId(10),
			commit_finalized_height: 50u32,
		};

		let update2 = NeighborPacket {
			round: Round(6),
			set_id: SetId(10),
			commit_finalized_height: 60,
		};

		let update3 = NeighborPacket {
			round: Round(2),
			set_id: SetId(11),
			commit_finalized_height: 61,
		};

		let update4 = NeighborPacket {
			round: Round(3),
			set_id: SetId(11),
			commit_finalized_height: 80,
		};

		let mut peers = Peers::default();
		let id = PeerId::random();

		peers.new_peer(id.clone());

		let mut check_update = move |update: NeighborPacket<_>| {
			let view = peers.update_peer_state(&id, update.clone()).unwrap().unwrap();
			assert_eq!(view.round, update.round);
			assert_eq!(view.set_id, update.set_id);
			assert_eq!(view.last_commit, Some(update.commit_finalized_height));
		};

		check_update(update1);
		check_update(update2);
		check_update(update3);
		check_update(update4);
	}

	#[test]
	fn invalid_view_change() {
		let mut peers = Peers::default();

		let id = PeerId::random();
		peers.new_peer(id.clone());

		peers.update_peer_state(&id, NeighborPacket {
			round: Round(10),
			set_id: SetId(10),
			commit_finalized_height: 10,
		}).unwrap().unwrap();

		let mut check_update = move |update: NeighborPacket<_>| {
			let err = peers.update_peer_state(&id, update.clone()).unwrap_err();
			assert_eq!(err, Misbehavior::InvalidViewChange);
		};

		// round moves backwards.
		check_update(NeighborPacket {
			round: Round(9),
			set_id: SetId(10),
			commit_finalized_height: 10,
		});
		// commit finalized height moves backwards.
		check_update(NeighborPacket {
			round: Round(10),
			set_id: SetId(10),
			commit_finalized_height: 9,
		});
		// set ID moves backwards.
		check_update(NeighborPacket {
			round: Round(10),
			set_id: SetId(9),
			commit_finalized_height: 10,
		});
	}

	#[test]
	fn messages_not_expired_immediately() {
		let (val, _) = GossipValidator::<Block>::new(config());

		let set_id = 1;

		val.note_set(SetId(set_id), Vec::new(), |_, _| {});

		for round_num in 1u64..10 {
			val.note_round(Round(round_num), |_, _| {});
		}

		{
			let mut is_expired = val.message_expired();
			let last_kept_round = 10u64 - KEEP_RECENT_ROUNDS as u64 - 1;

			// messages from old rounds are expired.
			for round_num in 1u64..last_kept_round {
				let topic = crate::communication::round_topic::<Block>(round_num, 1);
				assert!(is_expired(topic, &[1, 2, 3]));
			}

			// messages from not-too-old rounds are not expired.
			for round_num in last_kept_round..10 {
				let topic = crate::communication::round_topic::<Block>(round_num, 1);
				assert!(!is_expired(topic, &[1, 2, 3]));
			}
		}
	}

	#[test]
	fn message_from_unknown_authority_discarded() {
		assert!(cost::UNKNOWN_VOTER != cost::BAD_SIGNATURE);

		let (val, _) = GossipValidator::<Block>::new(config());
		let set_id = 1;
		let auth = AuthorityId::from_raw([1u8; 32]);
		let peer = PeerId::random();

		val.note_set(SetId(set_id), vec![auth.clone()], |_, _| {});
		val.note_round(Round(0), |_, _| {});

		let inner = val.inner.read();
		let unknown_voter = inner.validate_round_message(&peer, &VoteOrPrecommitMessage {
			round: Round(0),
			set_id: SetId(set_id),
			message: SignedMessage::<Block> {
				message: grandpa::Message::Prevote(grandpa::Prevote {
					target_hash: Default::default(),
					target_number: 10,
				}),
				signature: Default::default(),
				id: AuthorityId::from_raw([2u8; 32]),
			}
		});

		let bad_sig = inner.validate_round_message(&peer, &VoteOrPrecommitMessage {
			round: Round(0),
			set_id: SetId(set_id),
			message: SignedMessage::<Block> {
				message: grandpa::Message::Prevote(grandpa::Prevote {
					target_hash: Default::default(),
					target_number: 10,
				}),
				signature: Default::default(),
				id: auth.clone(),
			}
		});

		assert_eq!(unknown_voter, Action::Discard(cost::UNKNOWN_VOTER));
		assert_eq!(bad_sig, Action::Discard(cost::BAD_SIGNATURE));
	}
}
