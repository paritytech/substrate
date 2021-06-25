// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};
use log::{debug, trace};
use parking_lot::RwLock;

use sc_network::PeerId;
use sc_network_gossip::{MessageIntent, ValidationResult, Validator, ValidatorContext};

use sp_runtime::traits::{Block, Hash, Header, NumberFor};

use beefy_primitives::{
	crypto::{Public, Signature},
	MmrRootHash, VoteMessage,
};

use crate::keystore::BeefyKeystore;

// Limit BEEFY gossip by keeping only a bound number of voting rounds alive.
const MAX_LIVE_GOSSIP_ROUNDS: usize = 3;

/// Gossip engine messages topic
pub(crate) fn topic<B: Block>() -> B::Hash
where
	B: Block,
{
	<<B::Header as Header>::Hashing as Hash>::hash(b"beefy")
}

/// BEEFY gossip validator
///
/// Validate BEEFY gossip messages and limit the number of live BEEFY voting rounds.
///
/// Allows messages from last [`MAX_LIVE_GOSSIP_ROUNDS`] to flow, everything else gets
/// rejected/expired.
///
///All messaging is handled in a single BEEFY global topic.
pub(crate) struct GossipValidator<B>
where
	B: Block,
{
	topic: B::Hash,
	live_rounds: RwLock<Vec<NumberFor<B>>>,
}

impl<B> GossipValidator<B>
where
	B: Block,
{
	pub fn new() -> GossipValidator<B> {
		GossipValidator {
			topic: topic::<B>(),
			live_rounds: RwLock::new(Vec::new()),
		}
	}

	/// Note a voting round.
	///
	/// Noting `round` will keep `round` live.
	///
	/// We retain the [`MAX_LIVE_GOSSIP_ROUNDS`] most **recent** voting rounds as live.
	/// As long as a voting round is live, it will be gossiped to peer nodes.
	pub(crate) fn note_round(&self, round: NumberFor<B>) {
		trace!(target: "beefy", "🥩 About to note round #{}", round);

		let mut live = self.live_rounds.write();

		if let Some(idx) = live.binary_search(&round).err() {
			live.insert(idx, round);
		}

		if live.len() > MAX_LIVE_GOSSIP_ROUNDS {
			let _ = live.remove(0);
		}
	}

	fn is_live(live_rounds: &[NumberFor<B>], round: NumberFor<B>) -> bool {
		live_rounds.binary_search(&round).is_ok()
	}
}

impl<B> Validator<B> for GossipValidator<B>
where
	B: Block,
{
	fn validate(
		&self,
		_context: &mut dyn ValidatorContext<B>,
		sender: &PeerId,
		mut data: &[u8],
	) -> ValidationResult<B::Hash> {
		if let Ok(msg) = VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data) {
			if BeefyKeystore::verify(&msg.id, &msg.signature, &msg.commitment.encode()) {
				return ValidationResult::ProcessAndKeep(self.topic);
			} else {
				// TODO: report peer
				debug!(target: "beefy", "🥩 Bad signature on message: {:?}, from: {:?}", msg, sender);
			}
		}

		ValidationResult::Discard
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		let live_rounds = self.live_rounds.read();
		Box::new(move |_topic, mut data| {
			let msg = match VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let expired = !GossipValidator::<B>::is_live(&live_rounds, msg.commitment.block_number);

			trace!(target: "beefy", "🥩 Message for round #{} expired: {}", msg.commitment.block_number, expired);

			expired
		})
	}

	#[allow(clippy::type_complexity)]
	fn message_allowed<'a>(&'a self) -> Box<dyn FnMut(&PeerId, MessageIntent, &B::Hash, &[u8]) -> bool + 'a> {
		let live_rounds = self.live_rounds.read();
		Box::new(move |_who, _intent, _topic, mut data| {
			let msg = match VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let allowed = GossipValidator::<B>::is_live(&live_rounds, msg.commitment.block_number);

			trace!(target: "beefy", "🥩 Message for round #{} allowed: {}", msg.commitment.block_number, allowed);

			allowed
		})
	}
}

#[cfg(test)]
mod tests {
	use super::{GossipValidator, MAX_LIVE_GOSSIP_ROUNDS};
	use sc_network_test::Block;

	#[test]
	fn note_round_works() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(1u64);

		let live = gv.live_rounds.read();
		assert!(GossipValidator::<Block>::is_live(&live, 1u64));

		drop(live);

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		let live = gv.live_rounds.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(!GossipValidator::<Block>::is_live(&live, 1u64));
		assert!(GossipValidator::<Block>::is_live(&live, 3u64));
		assert!(GossipValidator::<Block>::is_live(&live, 7u64));
		assert!(GossipValidator::<Block>::is_live(&live, 10u64));
	}

	#[test]
	fn keeps_most_recent_max_rounds() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);
		gv.note_round(1u64);

		let live = gv.live_rounds.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, 3u64));
		assert!(!GossipValidator::<Block>::is_live(&live, 1u64));

		drop(live);

		gv.note_round(23u64);
		gv.note_round(15u64);
		gv.note_round(20u64);
		gv.note_round(2u64);

		let live = gv.live_rounds.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, 15u64));
		assert!(GossipValidator::<Block>::is_live(&live, 20u64));
		assert!(GossipValidator::<Block>::is_live(&live, 23u64));
	}

	#[test]
	fn note_same_round_twice() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		let live = gv.live_rounds.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		drop(live);

		// note round #7 again -> should not change anything
		gv.note_round(7u64);

		let live = gv.live_rounds.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, 3u64));
		assert!(GossipValidator::<Block>::is_live(&live, 7u64));
		assert!(GossipValidator::<Block>::is_live(&live, 10u64));
	}
}
