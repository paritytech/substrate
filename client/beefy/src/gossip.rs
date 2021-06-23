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

/// The maximum number of live gossip rounds allowed, i.e. we will expire messages older than this.
use codec::{Decode, Encode};
use log::{debug, trace};
use parking_lot::RwLock;

use sc_network::PeerId;
use sc_network_gossip::{
	MessageIntent, ValidationResult as GossipValidationResult, Validator as GossipValidator,
	ValidatorContext as GossipValidatorContext,
};

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
pub(crate) struct BeefyGossipValidator<B>
where
	B: Block,
{
	topic: B::Hash,
	live_rounds: RwLock<Vec<NumberFor<B>>>,
}

impl<B> BeefyGossipValidator<B>
where
	B: Block,
{
	pub fn new() -> BeefyGossipValidator<B> {
		BeefyGossipValidator {
			topic: topic::<B>(),
			live_rounds: RwLock::new(Vec::new()),
		}
	}

	/// Note a live voting round
	///
	/// This should be called, in order to keep tabs on `round`.
	pub(crate) fn note_round(&self, round: NumberFor<B>) {
		trace!(target: "beefy", "🥩 About to note round #{}", round);

		let mut live_rounds = self.live_rounds.write();

		// NOTE: ideally we'd use a VecDeque here, but currently binary search is only available on
		// nightly for `VecDeque`.
		while live_rounds.len() > MAX_LIVE_GOSSIP_ROUNDS {
			let _ = live_rounds.remove(0);
		}

		if let Some(idx) = live_rounds.binary_search(&round).err() {
			live_rounds.insert(idx, round);
		}
	}

	fn is_live(live_rounds: &[NumberFor<B>], round: NumberFor<B>) -> bool {
		live_rounds.binary_search(&round).is_ok()
	}
}

impl<B> GossipValidator<B> for BeefyGossipValidator<B>
where
	B: Block,
{
	fn validate(
		&self,
		_context: &mut dyn GossipValidatorContext<B>,
		sender: &sc_network::PeerId,
		mut data: &[u8],
	) -> GossipValidationResult<B::Hash> {
		if let Ok(msg) = VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data) {
			if BeefyKeystore::verify(&msg.id, &msg.signature, &msg.commitment.encode()) {
				return GossipValidationResult::ProcessAndKeep(self.topic);
			} else {
				// TODO: report peer
				debug!(target: "beefy", "🥩 Bad signature on message: {:?}, from: {:?}", msg, sender);
			}
		}

		GossipValidationResult::Discard
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		let live_rounds = self.live_rounds.read();
		Box::new(move |_topic, mut data| {
			let msg = match VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let expired = !BeefyGossipValidator::<B>::is_live(&live_rounds, msg.commitment.block_number);

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

			let allowed = BeefyGossipValidator::<B>::is_live(&live_rounds, msg.commitment.block_number);

			trace!(target: "beefy", "🥩 Message for round #{} allowed: {}", msg.commitment.block_number, allowed);

			allowed
		})
	}
}
