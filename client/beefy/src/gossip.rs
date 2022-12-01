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

#[cfg(test)]
mod tests {
	use sc_keystore::LocalKeystore;
	use sc_network_test::Block;
	use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

	use beefy_primitives::{crypto::Signature, Commitment, MmrRootHash, VoteMessage, KEY_TYPE};

	use crate::keystore::{tests::Keyring, BeefyKeystore};

	use super::*;

	#[test]
	fn note_round_works() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(1u64);

		let live = gv.known_votes.read();
		assert!(GossipValidator::<Block>::is_live(&live, &1u64));

		drop(live);

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		let live = gv.known_votes.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(!GossipValidator::<Block>::is_live(&live, &1u64));
		assert!(GossipValidator::<Block>::is_live(&live, &3u64));
		assert!(GossipValidator::<Block>::is_live(&live, &7u64));
		assert!(GossipValidator::<Block>::is_live(&live, &10u64));
	}

	#[test]
	fn keeps_most_recent_max_rounds() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);
		gv.note_round(1u64);

		let live = gv.known_votes.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, &3u64));
		assert!(!GossipValidator::<Block>::is_live(&live, &1u64));

		drop(live);

		gv.note_round(23u64);
		gv.note_round(15u64);
		gv.note_round(20u64);
		gv.note_round(2u64);

		let live = gv.known_votes.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, &15u64));
		assert!(GossipValidator::<Block>::is_live(&live, &20u64));
		assert!(GossipValidator::<Block>::is_live(&live, &23u64));
	}

	#[test]
	fn note_same_round_twice() {
		let gv = GossipValidator::<Block>::new();

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		let live = gv.known_votes.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		drop(live);

		// note round #7 again -> should not change anything
		gv.note_round(7u64);

		let live = gv.known_votes.read();

		assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		assert!(GossipValidator::<Block>::is_live(&live, &3u64));
		assert!(GossipValidator::<Block>::is_live(&live, &7u64));
		assert!(GossipValidator::<Block>::is_live(&live, &10u64));
	}

	struct TestContext;
	impl<B: sp_runtime::traits::Block> ValidatorContext<B> for TestContext {
		fn broadcast_topic(&mut self, _topic: B::Hash, _force: bool) {
			todo!()
		}

		fn broadcast_message(&mut self, _topic: B::Hash, _message: Vec<u8>, _force: bool) {
			todo!()
		}

		fn send_message(&mut self, _who: &sc_network::PeerId, _message: Vec<u8>) {
			todo!()
		}

		fn send_topic(&mut self, _who: &sc_network::PeerId, _topic: B::Hash, _force: bool) {
			todo!()
		}
	}

	fn sign_commitment<BN: Encode, P: Encode>(
		who: &Keyring,
		commitment: &Commitment<BN, P>,
	) -> Signature {
		let store: SyncCryptoStorePtr = std::sync::Arc::new(LocalKeystore::in_memory());
		SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&who.to_seed())).unwrap();
		let beefy_keystore: BeefyKeystore = Some(store).into();

		beefy_keystore.sign(&who.public(), &commitment.encode()).unwrap()
	}

	#[test]
	fn should_avoid_verifying_signatures_twice() {
		let gv = GossipValidator::<Block>::new();
		let sender = sc_network::PeerId::random();
		let mut context = TestContext;

		let commitment = Commitment {
			payload: MmrRootHash::default(),
			block_number: 3_u64,
			validator_set_id: 0,
		};

		let signature = sign_commitment(&Keyring::Alice, &commitment);

		let vote = VoteMessage { commitment, id: Keyring::Alice.public(), signature };

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		// first time the cache should be populated.
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		assert_eq!(
			gv.known_votes.read().get(&vote.commitment.block_number).map(|x| x.len()),
			Some(1)
		);

		// second time we should hit the cache
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// next we should quickly reject if the round is not live.
		gv.note_round(11_u64);
		gv.note_round(12_u64);

		assert!(!GossipValidator::<Block>::is_live(
			&*gv.known_votes.read(),
			&vote.commitment.block_number
		));

		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::Discard));
	}
}
