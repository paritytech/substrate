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

	/// Consider a commit. Rounds are not taken into account, but are implicitly
	/// because we gate on finalization of a further block than a previous commit.
	pub fn consider_commit(&self, set_id: SetId, number: N) -> Consider {
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
		self.inner.insert(node_index, PeerInfo { view: View::default() });
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
}

enum Action<H>  {
	// repropagate under given topic, to the given peers, applying cost/benefit to originator.
	Repropagate(H, i32),
	// discard, applying cost/benefit to originator.
	Discard(i32),
}

/// A validator for GRANDPA gossip messages.
pub(crate) struct GossipValidator<Block: BlockT> {
	local_view: parking_lot::RwLock<View<NumberFor<Block>>>,
	peers: parking_lot::RwLock<Peers<NumberFor<Block>>>,
	_marker: std::marker::PhantomData<Block>,
}

impl<Block: BlockT> GossipValidator<Block> {
	/// Create a new gossip-validator.
	pub(crate) fn new() -> GossipValidator<Block> {
		GossipValidator {
			local_view: parking_lot::RwLock::new(View::default()),
			peers: parking_lot::RwLock::new(Peers { inner: Default::default() }),
			_marker: Default::default(),
		}
	}

	/// Note a round in a set has started.
	pub(crate) fn note_round(&self, round: Round, set_id: SetId) {
		let mut view = self.local_view.write();
		view.round = round;

		if set_id != view.set_id {
			// clear commit when we change set.
			view.last_commit = None;
		}

		view.set_id = set_id;
	}

	/// Note that a voter set with given ID has started.
	pub(crate) fn note_set(&self, set_id: SetId) {
		self.local_view.write().update_set(set_id);
	}

	/// Note that we've imported a commit finalizing a given block.
	pub(crate) fn note_commit_finalized(&self, finalized: NumberFor<Block>) {
		let mut view = self.local_view.write();
		view.last_commit = std::cmp::max(view.last_commit, Some(finalized));
	}

	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		self.local_view.read().consider_vote(round, set_id)
	}

	fn consider_commit(&self, set_id: SetId, number: NumberFor<Block>) -> Consider {
		self.local_view.read().consider_commit(set_id, number)
	}

	fn cost_past_rejection(&self, _who: &NodeIndex, _round: Round, _set_id: SetId) -> i32 {
		-50 // hardcode for now.
	}

	fn report(&self, _who: NodeIndex, _cost_benefit: i32) {
		// nothing yet.
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

		let topic = super::message_topic::<Block>(full.round.0, full.set_id.0);
		Action::Repropagate(topic, 100)
	}

	fn validate_commit_message(&self, who: &NodeIndex, full: &FullCommitMessage<Block>)
		-> Action<Block::Hash>
	{
		use grandpa::Message as GrandpaMessage;

		match self.consider_commit(full.set_id, full.message.target_number) {
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

		let topic = super::commit_topic::<Block>(full.set_id.0);
		Action::Repropagate(topic, 100)
	}
}

impl<Block: BlockT> network_gossip::Validator<Block> for GossipValidator<Block> {
	fn new_peer(&self, _context: &mut ValidatorContext<Block>, who: NodeIndex, _roles: Roles) {
		self.peers.write().new_peer(who);
	}

	fn peer_disconnected(&self, _context: &mut ValidatorContext<Block>, who: NodeIndex) {
		self.peers.write().peer_disconnected(&who);
	}

	fn validate(&self, context: &mut ValidatorContext<Block>, who: NodeIndex, mut data: &[u8])
		-> network_gossip::ValidationResult<Block::Hash>
	{
		let action = match GossipMessage::<Block>::decode(&mut data) {
			Some(GossipMessage::VoteOrPrecommit(ref message))
				=> self.validate_round_message(&who, message),
			Some(GossipMessage::Commit(ref message)) => self.validate_commit_message(&who, message),
			Some(GossipMessage::Neighbor(_)) => unimplemented!(),
			None => {
				debug!(target: "afg", "Error decoding message");
				telemetry!(CONSENSUS_DEBUG; "afg.err_decoding_msg"; "" => "");

				let len = std::cmp::min(i32::max_value() as usize, data.len()) as i32;
				Action::Discard(Misbehavior::UndecodablePacket(len).cost())
			}
		};

		if let Action::Repropagate(ref topic, _) = action {
			context.broadcast_message(*topic, data.to_vec(), false);
		}

		match action {
			Action::Repropagate(topic, cb) => {
				self.report(who, cb);
				network_gossip::ValidationResult::ValidStored(topic)
			}
			Action::Discard(cb) => {
				self.report(who, cb);
				network_gossip::ValidationResult::ValidOneHop
			}
		}
	}

	fn should_send_to(&self, _who: NodeIndex, _topic: &Block::Hash, _data: &[u8]) -> bool {
		true
	}

	fn message_expired<'a>(&'a self) -> Box<FnMut(Block::Hash, &[u8]) -> bool + 'a> {
		let rounds = self.local_view.read();
		Box::new(move |_topic, mut data| {
			let consider = match GossipMessage::<Block>::decode(&mut data) {
				None => Consider::Accept,
				Some(GossipMessage::Commit(full)) => rounds.consider_commit(
					full.set_id,
					full.message.target_number,
				),
				Some(GossipMessage::VoteOrPrecommit(full)) =>
					rounds.consider_vote(full.round, full.set_id),
				Some(GossipMessage::Neighbor(_)) => Consider::RejectPast,
			};

			consider == Consider::Accept
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
	fn commit_vote_rules() {
		let view = View { round: Round(100), set_id: SetId(2), last_commit: Some(1000u64) };

		assert_eq!(view.consider_commit(Round(3), SetId(1)), Consider::RejectFuture);
		assert_eq!(view.consider_commit(Round(3), SetId(1000)), Consider::RejectFuture);
		assert_eq!(view.consider_commit(Round(3), SetId(10000)), Consider::RejectFuture);

		assert_eq!(view.consider_commit(Round(1), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_commit(Round(1), SetId(1000)), Consider::RejectPast);
		assert_eq!(view.consider_commit(Round(1), SetId(10000)), Consider::RejectPast);

		assert_eq!(view.consider_commit(Round(2), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_commit(Round(2), SetId(1000)), Consider::RejectPast);
		assert_eq!(view.consider_commit(Round(2), SetId(1001)), Consider::Accept);
		assert_eq!(view.consider_commit(Round(2), SetId(10000)), Consider::Accept);
	}
}
