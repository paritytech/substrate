// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use std::{collections::BTreeMap, time::Duration};

use sc_network::PeerId;
use sc_network_gossip::{MessageIntent, ValidationResult, Validator, ValidatorContext};
use sp_core::hashing::twox_64;
use sp_runtime::traits::{Block, Hash, Header, NumberFor};

use codec::{Decode, Encode};
use log::{debug, trace};
use parking_lot::{Mutex, RwLock};
use wasm_timer::Instant;

use beefy_primitives::{
	crypto::{Public, Signature},
	MmrRootHash, VoteMessage,
};

use crate::keystore::BeefyKeystore;

#[cfg(test)]
#[path = "gossip_tests.rs"]
mod tests;

// Limit BEEFY gossip by keeping only a bound number of voting rounds alive.
const MAX_LIVE_GOSSIP_ROUNDS: usize = 3;

// Timeout for rebroadcasting messages.
const REBROADCAST_AFTER: Duration = Duration::from_secs(60 * 5);

/// Gossip engine messages topic
pub(crate) fn topic<B: Block>() -> B::Hash
where
	B: Block,
{
	<<B::Header as Header>::Hashing as Hash>::hash(b"beefy")
}

/// A type that represents hash of the message.
pub type MessageHash = [u8; 8];

type KnownVotes<B> = BTreeMap<NumberFor<B>, fnv::FnvHashSet<MessageHash>>;

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
	known_votes: RwLock<KnownVotes<B>>,
	next_rebroadcast: Mutex<Instant>,
}

impl<B> GossipValidator<B>
where
	B: Block,
{
	pub fn new() -> GossipValidator<B> {
		GossipValidator {
			topic: topic::<B>(),
			known_votes: RwLock::new(BTreeMap::new()),
			next_rebroadcast: Mutex::new(Instant::now() + REBROADCAST_AFTER),
		}
	}

	/// Note a voting round.
	///
	/// Noting `round` will keep `round` live.
	///
	/// We retain the [`MAX_LIVE_GOSSIP_ROUNDS`] most **recent** voting rounds as live.
	/// As long as a voting round is live, it will be gossiped to peer nodes.
	pub(crate) fn note_round(&self, round: NumberFor<B>) {
		debug!(target: "beefy", "🥩 About to note round #{}", round);

		let mut live = self.known_votes.write();

		if !live.contains_key(&round) {
			live.insert(round, Default::default());
		}

		if live.len() > MAX_LIVE_GOSSIP_ROUNDS {
			let to_remove = live.iter().next().map(|x| x.0).copied();
			if let Some(first) = to_remove {
				live.remove(&first);
			}
		}
	}

	fn add_known(known_votes: &mut KnownVotes<B>, round: &NumberFor<B>, hash: MessageHash) {
		known_votes.get_mut(round).map(|known| known.insert(hash));
	}

	// Note that we will always keep the most recent unseen round alive.
	//
	// This is a preliminary fix and the detailed description why we are
	// doing this can be found as part of the issue below
	//
	// https://github.com/paritytech/grandpa-bridge-gadget/issues/237
	//
	fn is_live(known_votes: &KnownVotes<B>, round: &NumberFor<B>) -> bool {
		let unseen_round = if let Some(max_known_round) = known_votes.keys().last() {
			round > max_known_round
		} else {
			known_votes.is_empty()
		};

		known_votes.contains_key(round) || unseen_round
	}

	fn is_known(known_votes: &KnownVotes<B>, round: &NumberFor<B>, hash: &MessageHash) -> bool {
		known_votes.get(round).map(|known| known.contains(hash)).unwrap_or(false)
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
		if let Ok(msg) =
			VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(&mut data)
		{
			let msg_hash = twox_64(data);
			let round = msg.commitment.block_number;

			// Verify general usefulness of the message.
			// We are going to discard old votes right away (without verification)
			// Also we keep track of already received votes to avoid verifying duplicates.
			{
				let known_votes = self.known_votes.read();

				if !GossipValidator::<B>::is_live(&known_votes, &round) {
					return ValidationResult::Discard
				}

				if GossipValidator::<B>::is_known(&known_votes, &round, &msg_hash) {
					return ValidationResult::ProcessAndKeep(self.topic)
				}
			}

			if BeefyKeystore::verify(&msg.id, &msg.signature, &msg.commitment.encode()) {
				GossipValidator::<B>::add_known(&mut *self.known_votes.write(), &round, msg_hash);
				return ValidationResult::ProcessAndKeep(self.topic)
			} else {
				// TODO: report peer
				debug!(target: "beefy", "🥩 Bad signature on message: {:?}, from: {:?}", msg, sender);
			}
		}

		ValidationResult::Discard
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		let known_votes = self.known_votes.read();
		Box::new(move |_topic, mut data| {
			let msg = match VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(
				&mut data,
			) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let round = msg.commitment.block_number;
			let expired = !GossipValidator::<B>::is_live(&known_votes, &round);

			trace!(target: "beefy", "🥩 Message for round #{} expired: {}", round, expired);

			expired
		})
	}

	fn message_allowed<'a>(
		&'a self,
	) -> Box<dyn FnMut(&PeerId, MessageIntent, &B::Hash, &[u8]) -> bool + 'a> {
		let do_rebroadcast = {
			let now = Instant::now();
			let mut next_rebroadcast = self.next_rebroadcast.lock();
			if now >= *next_rebroadcast {
				*next_rebroadcast = now + REBROADCAST_AFTER;
				true
			} else {
				false
			}
		};

		let known_votes = self.known_votes.read();
		Box::new(move |_who, intent, _topic, mut data| {
			if let MessageIntent::PeriodicRebroadcast = intent {
				return do_rebroadcast
			}

			let msg = match VoteMessage::<MmrRootHash, NumberFor<B>, Public, Signature>::decode(
				&mut data,
			) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let round = msg.commitment.block_number;
			let allowed = GossipValidator::<B>::is_live(&known_votes, &round);

			debug!(target: "beefy", "🥩 Message for round #{} allowed: {}", round, allowed);

			allowed
		})
	}
}
