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

//! Gossip and politeness for GRANDPA communication.

use runtime_primitives::traits::{NumberFor, Block as BlockT};
use network::consensus_gossip::{self as network_gossip, ValidatorContext};
use network::{config::Roles, NodeIndex};
use parity_codec::{Encode, Decode};

use substrate_telemetry::{telemetry, CONSENSUS_DEBUG};
use log::debug;

use crate::{CompactCommit, SignedMessage};
use super::{Round, SetId};

use std::collections::HashMap;

/// An outcome of examining a message.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Consider {
	/// Accept the message.
	Accept,
	/// Message is too early. Reject.
	RejectPast,
	/// Message is from the future. Reject.
	RejectFuture,
}

/// A view of protocol state.
pub struct View<N> {
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
	pub fn update_set(&mut self, set_id: SetId) {
		self.set_id = set_id;
		self.round = Round(0);
	}

	/// Consider a round and set ID combination under a current view.
	pub fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
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
	pub fn consider_global(&self, set_id: SetId, number: N) -> Consider {
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

	// the previous round, if we're not at 0.
	fn prev_round(&self) -> Option<Round> {
		if self.round.0 == 0 {
			None
		} else {
			Some(Round(self.round.0 - 1))
		}
	}
}

fn view_topics<B: BlockT>(view: &View<NumberFor<B>>) -> HashMap<B::Hash, (Option<Round>, SetId)> {
	let s = view.set_id;
	let mut map: HashMap<_, _> = [
		(super::global_topic::<B>(s.0), (None, s)),
		(super::round_topic::<B>(view.round.0, s.0), (Some(view.round), s)),
	].iter().cloned().collect();

	if let Some(r) = view.prev_round() {
		map.insert(super::round_topic::<B>(r.0, s.0), (Some(r), s));
	}

	map
}

/// Grandpa gossip message type.
/// This is the root type that gets encoded and sent on the network.
#[derive(Debug, Encode, Decode)]
pub enum GossipMessage<Block: BlockT> {
	/// Grandpa message with round and set info.
	VoteOrPrecommit(VoteOrPrecommitMessage<Block>),
	/// Grandpa commit message with round and set info.
	Commit(FullCommitMessage<Block>),
	/// A neighbor packet. Not repropagated.
	Neighbor(NeighborPacket<NumberFor<Block>>),
}

/// Network level message with topic information.
#[derive(Debug, Encode, Decode)]
pub struct VoteOrPrecommitMessage<Block: BlockT> {
	/// The round this message is from.
	pub round: Round,
	/// The voter set ID this message is from.
	pub set_id: SetId,
	/// The message itself.
	pub message: SignedMessage<Block>,
}

/// Network level commit message with topic information.
#[derive(Debug, Encode, Decode)]
pub struct FullCommitMessage<Block: BlockT> {
	/// The round this message is from.
	pub round: Round,
	/// The voter set ID this message is from.
	pub set_id: SetId,
	/// The compact commit message.
	pub message: CompactCommit<Block>,
}

/// V1 neighbor packet. Neighbor packets are sent from nodes to their peers
/// and are not repropagated. These contain information about the node's state.
#[derive(Debug, Encode, Decode)]
pub struct NeighborPacket<N> {
	round: Round,
	set_id: SetId,
	finalized_height: N,
	commit_finalized_height: N,
}

/// A versioned neighbor packet.
#[derive(Debug, Encode, Decode)]
pub enum VersionedNeighborPacket<N> {
	#[codec(index = "1")]
	V1(NeighborPacket<N>),
}

/// Misbehavior that peers can perform.
///
/// `cost` gives a cost that can be used to perform cost/benefit analysis of a
/// peer.
#[derive(Clone, Copy, Debug)]
enum Misbehavior {
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
	// Commit message received that's behind local view.
	OldCommitMessage,
	// A message received that's from the future relative to our view.
	// always misbehavior.
	FutureMessage,
}

impl Misbehavior {
	fn cost(&self) -> i32 {
		use Misbehavior::*;

		match *self {
			InvalidViewChange => -500,
			UndecodablePacket(bytes) =>  bytes.saturating_mul(-5),
			BadCommitMessage { signatures_checked, blocks_loaded, equivocations_caught } => {
				let cost = 25i32.saturating_mul(signatures_checked)
					.saturating_add(10i32.saturating_mul(blocks_loaded));
				let benefit = equivocations_caught.saturating_mul(10);

				(benefit as i32).saturating_sub(cost as i32)
			},
			OldCommitMessage => -100,
			FutureMessage => -500,
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
	inner: HashMap<NodeIndex, PeerInfo<N>>,
}

impl<N: Ord> Peers<N> {
	fn new_peer(&mut self, node_index: NodeIndex) {
		self.inner.insert(node_index, PeerInfo::new());
	}

	fn peer_disconnected(&mut self, node_index: &NodeIndex) {
		self.inner.remove(node_index);
	}

	fn update_peer_state(&mut self, node_index: &NodeIndex, update: NeighborPacket<N>) -> Result<(), Misbehavior> {
		let peer = match self.inner.get_mut(node_index) {
			None => return Ok(()),
			Some(p) => p,
		};

		let invalid_change = peer.view.set_id > update.set_id
			|| peer.view.round > update.round && peer.view.set_id == peer.view.set_id
			|| update.commit_finalized_height > update.finalized_height
			|| peer.view.last_commit.as_ref() > Some(&update.commit_finalized_height);

		if invalid_change {
			return Err(Misbehavior::InvalidViewChange);
		}

		peer.view = View {
			round: update.round,
			set_id: update.set_id,
			last_commit: Some(update.commit_finalized_height),
		};

		Ok(())
	}

	fn peer<'a>(&'a self, node_index: &NodeIndex) -> Option<&'a PeerInfo<N>> {
		self.inner.get(node_index)
	}
}

enum Action<H>  {
	// repropagate under given topic, to the given peers, applying cost/benefit to originator.
	Repropagate(H, i32),
	// discard, applying cost/benefit to originator.
	Discard(i32),
}

struct Inner<Block: BlockT> {
	local_view: View<NumberFor<Block>>,
	peers: Peers<NumberFor<Block>>,
	live_topics: HashMap<Block::Hash, (Option<Round>, SetId)>,

}

impl<Block: BlockT> Inner<Block> {
	fn new() -> Self {
		Inner {
			local_view: View::default(),
			peers: Peers { inner: HashMap::new() },
			live_topics: HashMap::new(),
		}
	}

	fn update_view_topics(&mut self) {
		self.live_topics = view_topics::<Block>(&self.local_view);
	}

	/// Note a round in a set has started.
	fn note_round(&mut self, round: Round, set_id: SetId) {
		self.local_view.round = round;

		if set_id != self.local_view.set_id {
			// clear commit when we change set.
			self.local_view.last_commit = None;
		}

		self.local_view.set_id = set_id;
		self.update_view_topics();
	}

	/// Note that a voter set with given ID has started.
	fn note_set(&mut self, set_id: SetId) {
		self.local_view.update_set(set_id);
		self.update_view_topics();
	}

	/// Note that we've imported a commit finalizing a given block.
	fn note_commit_finalized(&mut self, finalized: NumberFor<Block>) {
		self.local_view.last_commit = std::cmp::max(self.local_view.last_commit, Some(finalized));
	}

	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		self.local_view.consider_vote(round, set_id)
	}

	fn consider_global(&self, set_id: SetId, number: NumberFor<Block>) -> Consider {
		self.local_view.consider_global(set_id, number)
	}

	fn cost_past_rejection(&self, _who: &NodeIndex, _round: Round, _set_id: SetId) -> i32 {
		-50 // hardcode for now.
	}

	fn validate_round_message(&self, who: &NodeIndex, full: &VoteOrPrecommitMessage<Block>)
		-> Action<Block::Hash>
	{
		match self.consider_vote(full.round, full.set_id) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::Accept => {},
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
			return Action::Discard(-100);
		}

		let topic = super::round_topic::<Block>(full.round.0, full.set_id.0);
		Action::Repropagate(topic, 100)
	}

	fn validate_commit_message(&self, who: &NodeIndex, full: &FullCommitMessage<Block>)
		-> Action<Block::Hash>
	{
		use grandpa::Message as GrandpaMessage;

		match self.consider_global(full.set_id, full.message.target_number) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::Accept => {},
		}

		if full.message.precommits.len() != full.message.auth_data.len() || full.message.precommits.is_empty() {
			debug!(target: "afg", "Malformed compact commit");
			telemetry!(CONSENSUS_DEBUG; "afg.malformed_compact_commit";
				"precommits_len" => ?full.message.precommits.len(),
				"auth_data_len" => ?full.message.auth_data.len(),
				"precommits_is_empty" => ?full.message.precommits.is_empty(),
			);
			return Action::Discard(-1000);
		}

		// check signatures on all contained precommits.
		for (i, (precommit, &(ref sig, ref id))) in full.message.precommits.iter()
			.zip(&full.message.auth_data)
			.enumerate()
		{
			if let Err(()) = super::check_message_sig::<Block>(
				&GrandpaMessage::Precommit(precommit.clone()),
				id,
				sig,
				full.round.0,
				full.set_id.0,
			) {
				debug!(target: "afg", "Bad commit message signature {}", id);
				telemetry!(CONSENSUS_DEBUG; "afg.bad_commit_msg_signature"; "id" => ?id);
				return Action::Discard(Misbehavior::BadCommitMessage {
					signatures_checked: i as i32,
					blocks_loaded: 0,
					equivocations_caught: 0,
				}.cost());
			}
		}

		// always discard commits initially and rebroadcast after doing full
		// checking.
		//
		// TODO: make this "DiscardAndProcess"
		let _topic = super::global_topic::<Block>(full.set_id.0);
		Action::Discard(100)
	}

	fn import_neighbor_message(&mut self, who: &NodeIndex, update: NeighborPacket<NumberFor<Block>>)
		-> Action<Block::Hash>
	{
		let cb = match self.peers.update_peer_state(who, update) {
			Ok(()) => 100i32,
			Err(misbehavior) => misbehavior.cost(),
		};

		// always discard, it's valid for one hop.
		Action::Discard(cb)
	}
}

/// A validator for GRANDPA gossip messages.
pub(crate) struct GossipValidator<Block: BlockT> {
	inner: parking_lot::RwLock<Inner<Block>>,
}

impl<Block: BlockT> GossipValidator<Block> {
	/// Create a new gossip-validator.
	pub(crate) fn new() -> GossipValidator<Block> {
		GossipValidator { inner: parking_lot::RwLock::new(Inner::new()) }
	}

	/// Note a round in a set has started.
	pub(crate) fn note_round(&self, round: Round, set_id: SetId) {
		self.inner.write().note_round(round, set_id);
	}

	/// Note that a voter set with given ID has started.
	pub(crate) fn note_set(&self, set_id: SetId) {
		self.inner.write().note_set(set_id);
	}

	/// Note that we've imported a commit finalizing a given block.
	pub(crate) fn note_commit_finalized(&self, finalized: NumberFor<Block>) {
		self.inner.write().note_commit_finalized(finalized);
	}

	fn report(&self, _who: NodeIndex, _cost_benefit: i32) {
		// nothing yet.
	}
}

impl<Block: BlockT> network_gossip::Validator<Block> for GossipValidator<Block> {
	fn new_peer(&self, _context: &mut ValidatorContext<Block>, who: NodeIndex, _roles: Roles) {
		self.inner.write().peers.new_peer(who);
	}

	fn peer_disconnected(&self, _context: &mut ValidatorContext<Block>, who: NodeIndex) {
		self.inner.write().peers.peer_disconnected(&who);
	}

	fn validate(&self, context: &mut ValidatorContext<Block>, who: NodeIndex, mut data: &[u8])
		-> network_gossip::ValidationResult<Block::Hash>
	{
		let action = {
			let mut inner = self.inner.write();
			match GossipMessage::<Block>::decode(&mut data) {
				Some(GossipMessage::VoteOrPrecommit(ref message))
					=> inner.validate_round_message(&who, message),
				Some(GossipMessage::Commit(ref message)) => inner.validate_commit_message(&who, message),
				Some(GossipMessage::Neighbor(update)) => inner.import_neighbor_message(&who, update),
				None => {
					debug!(target: "afg", "Error decoding message");
					telemetry!(CONSENSUS_DEBUG; "afg.err_decoding_msg"; "" => "");

					let len = std::cmp::min(i32::max_value() as usize, data.len()) as i32;
					Action::Discard(Misbehavior::UndecodablePacket(len).cost())
				}
			}
		};

		if let Action::Repropagate(ref topic, _) = action {
			context.broadcast_message(*topic, data.to_vec(), false);
		}

		match action {
			Action::Repropagate(topic, cb) => {
				self.report(who, cb);
				network_gossip::ValidationResult::Keep(topic)
			}
			Action::Discard(cb) => {
				self.report(who, cb);
				network_gossip::ValidationResult::Discard
			}
		}
	}

	fn should_send_to<'a>(&'a self) -> Box<FnMut(NodeIndex, Block::Hash, &[u8]) -> bool + 'a> {
		let inner = self.inner.read();
		Box::new(move |who, topic, mut data| {
			let peer = match inner.peers.peer(&who) {
				None => return false,
				Some(x) => x,
			};

			// if the topic is not something we're keeping at the moment,
			// do not send.
			let &(ref maybe_round, ref set_id) = match inner.live_topics.get(&topic) {
				None => return false,
				Some(x) => x,
			};

			// if the topic is not something the peer accepts, discard.
			if let Some(round) = maybe_round {
				return peer.view.consider_vote(*round, *set_id) == Consider::Accept
			}

			// global message.
			let our_best_commit = inner.local_view.last_commit;
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

	fn message_expired<'a>(&'a self) -> Box<FnMut(Block::Hash, &[u8]) -> bool + 'a> {
		let inner = self.inner.read();
		Box::new(move |topic, mut data| {
			// if the topic is not one of the ones that we are keeping at the moment,
			// it is expired.
			let &(ref maybe_round, _) = match inner.live_topics.get(&topic) {
				None => return true,
				Some(x) => x,
			};

			// round messages don't require any further checking.
			if maybe_round.is_none() { return false }

			// global messages -- only keep the best commit.
			let best_commit = inner.local_view.last_commit;

			match GossipMessage::<Block>::decode(&mut data) {
				None => true,
				Some(GossipMessage::Commit(full))
					=> Some(full.message.target_number) != best_commit,
				Some(_) => true,
			}
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;

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

		assert_eq!(view.consider_global(Round(3), SetId(1)), Consider::RejectFuture);
		assert_eq!(view.consider_global(Round(3), SetId(1000)), Consider::RejectFuture);
		assert_eq!(view.consider_global(Round(3), SetId(10000)), Consider::RejectFuture);

		assert_eq!(view.consider_global(Round(1), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_global(Round(1), SetId(1000)), Consider::RejectPast);
		assert_eq!(view.consider_global(Round(1), SetId(10000)), Consider::RejectPast);

		assert_eq!(view.consider_global(Round(2), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_global(Round(2), SetId(1000)), Consider::RejectPast);
		assert_eq!(view.consider_global(Round(2), SetId(1001)), Consider::Accept);
		assert_eq!(view.consider_global(Round(2), SetId(10000)), Consider::Accept);
	}
}
