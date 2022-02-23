// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
	VoteMessage,
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

struct KnownVotes<B: Block> {
	last_done: Option<NumberFor<B>>,
	live: BTreeMap<NumberFor<B>, fnv::FnvHashSet<MessageHash>>,
}

impl<B: Block> KnownVotes<B> {
	pub fn new() -> Self {
		Self { last_done: None, live: BTreeMap::new() }
	}

	/// Create new round votes set if not already present.
	///
	/// Only [`MAX_LIVE_GOSSIP_ROUNDS`] most **recent** voting rounds sets are kept.
	pub fn insert(&mut self, round: NumberFor<B>) {
		let live = &mut self.live;

		if !live.contains_key(&round) {
			live.insert(round, Default::default());
		}

		if live.len() > MAX_LIVE_GOSSIP_ROUNDS {
			let to_remove = live.iter().next().map(|x| x.0).copied();
			if let Some(first) = to_remove {
				self.remove(first.clone());
			}
		}
	}

	pub fn remove(&mut self, round: NumberFor<B>) {
		self.live.remove(&round);
		self.last_done = self.last_done.max(Some(round));
	}
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
			known_votes: RwLock::new(KnownVotes::new()),
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
		debug!(target: "beefy", "🥩 About to note gossip round #{}", round);
		self.known_votes.write().insert(round);
	}

	/// Drop a voting round.
	///
	/// This can be called once round is complete so we stop gossiping for it.
	pub(crate) fn drop_round(&self, round: NumberFor<B>) {
		debug!(target: "beefy", "🥩 About to drop gossip round #{}", round);
		self.known_votes.write().remove(round);
	}

	// Return true if `round` is live or if it is newer than previously seen rounds.
	fn is_live(known_votes: &KnownVotes<B>, round: &NumberFor<B>) -> bool {
		let unseen_round = if let Some(max_known_round) = known_votes.live.keys().last() {
			round > max_known_round
		} else {
			Some(*round) > known_votes.last_done
		};

		unseen_round || known_votes.live.contains_key(round)
	}

	// Add new _known_ `hash` to the round's known votes.
	fn add_known(known_votes: &mut KnownVotes<B>, round: &NumberFor<B>, hash: MessageHash) {
		known_votes.live.get_mut(round).map(|known| known.insert(hash));
	}

	// Check if `hash` is already part of round's known votes.
	fn is_known(known_votes: &KnownVotes<B>, round: &NumberFor<B>, hash: &MessageHash) -> bool {
		known_votes.live.get(round).map(|known| known.contains(hash)).unwrap_or(false)
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
		if let Ok(msg) = VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
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
			let msg = match VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
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
		let do_rebroadcast = || {
			let now = Instant::now();
			// TODO: right now we're using an object-level rebroadcast gate that will only
			// allow **a single message** being rebroadcast every `REBROADCAST_AFTER` minutes.
			//
			// Should we instead have a per-message/hash rebroadcast cooldown?
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
				return do_rebroadcast()
			}

			let msg = match VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return false,
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

	use crate::keystore::{tests::Keyring, BeefyKeystore};
	use beefy_primitives::{
		crypto::Signature, known_payload_ids, Commitment, MmrRootHash, Payload, VoteMessage,
		KEY_TYPE,
	};

	use super::*;

	#[test]
	fn known_votes_insert_remove() {
		let mut kv = KnownVotes::<Block>::new();

		kv.insert(1);
		kv.insert(1);
		kv.insert(2);
		assert_eq!(kv.live.len(), 2);

		for i in 1..MAX_LIVE_GOSSIP_ROUNDS + 2 {
			kv.insert(i.try_into().unwrap());
		}
		assert_eq!(kv.live.len(), MAX_LIVE_GOSSIP_ROUNDS);

		let mut kv = KnownVotes::<Block>::new();
		kv.insert(1);
		kv.insert(2);
		kv.insert(3);

		assert!(kv.last_done.is_none());
		kv.remove(2);
		assert_eq!(kv.live.len(), 2);
		assert!(!kv.live.contains_key(&2));
		assert_eq!(kv.last_done, Some(2));

		kv.remove(1);
		assert_eq!(kv.last_done, Some(2));

		kv.remove(3);
		assert_eq!(kv.last_done, Some(3));
		assert!(kv.live.is_empty());
	}

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

		assert_eq!(live.live.len(), MAX_LIVE_GOSSIP_ROUNDS);

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
		assert_eq!(live.live.len(), MAX_LIVE_GOSSIP_ROUNDS);
		assert!(GossipValidator::<Block>::is_live(&live, &3u64));
		assert!(!GossipValidator::<Block>::is_live(&live, &1u64));
		drop(live);

		gv.note_round(23u64);
		gv.note_round(15u64);
		gv.note_round(20u64);
		gv.note_round(2u64);

		let live = gv.known_votes.read();

		assert_eq!(live.live.len(), MAX_LIVE_GOSSIP_ROUNDS);

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
		assert_eq!(live.live.len(), MAX_LIVE_GOSSIP_ROUNDS);
		drop(live);

		// note round #7 again -> should not change anything
		gv.note_round(7u64);

		let live = gv.known_votes.read();

		assert_eq!(live.live.len(), MAX_LIVE_GOSSIP_ROUNDS);

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

	fn sign_commitment<BN: Encode>(who: &Keyring, commitment: &Commitment<BN>) -> Signature {
		let store: SyncCryptoStorePtr = std::sync::Arc::new(LocalKeystore::in_memory());
		SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&who.to_seed())).unwrap();
		let beefy_keystore: BeefyKeystore = Some(store).into();

		beefy_keystore.sign(&who.public(), &commitment.encode()).unwrap()
	}

	fn dummy_vote(block_number: u64) -> VoteMessage<u64, Public, Signature> {
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, MmrRootHash::default().encode());
		let commitment = Commitment { payload, block_number, validator_set_id: 0 };
		let signature = sign_commitment(&Keyring::Alice, &commitment);

		VoteMessage { commitment, id: Keyring::Alice.public(), signature }
	}

	#[test]
	fn should_avoid_verifying_signatures_twice() {
		let gv = GossipValidator::<Block>::new();
		let sender = sc_network::PeerId::random();
		let mut context = TestContext;

		let vote = dummy_vote(3);

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		// first time the cache should be populated
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		assert_eq!(
			gv.known_votes.read().live.get(&vote.commitment.block_number).map(|x| x.len()),
			Some(1)
		);

		// second time we should hit the cache
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// next we should quickly reject if the round is not live
		gv.note_round(11_u64);
		gv.note_round(12_u64);

		assert!(!GossipValidator::<Block>::is_live(
			&*gv.known_votes.read(),
			&vote.commitment.block_number
		));

		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::Discard));
	}

	#[test]
	fn messages_allowed_and_expired() {
		let gv = GossipValidator::<Block>::new();
		let sender = sc_network::PeerId::random();
		let topic = Default::default();
		let intent = MessageIntent::Broadcast;

		// note round 2
		gv.note_round(2u64);
		let mut allowed = gv.message_allowed();
		let mut expired = gv.message_expired();

		// check bad vote format
		assert!(!allowed(&sender, intent, &topic, &mut [0u8; 16]));
		assert!(expired(topic, &mut [0u8; 16]));

		// inactive round 1 -> expired
		let vote = dummy_vote(1);
		let mut encoded_vote = vote.encode();
		assert!(!allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(expired(topic, &mut encoded_vote));

		// active round 2 -> !expired
		let vote = dummy_vote(2);
		let mut encoded_vote = vote.encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));

		// unseen round 3 -> !expired
		let vote = dummy_vote(3);
		let mut encoded_vote = vote.encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));
	}

	#[test]
	fn messages_rebroadcast() {
		let gv = GossipValidator::<Block>::new();
		let sender = sc_network::PeerId::random();
		let topic = Default::default();

		let vote = dummy_vote(1);
		let mut encoded_vote = vote.encode();

		// re-broadcasting only allowed at `REBROADCAST_AFTER` intervals
		let intent = MessageIntent::PeriodicRebroadcast;
		let mut allowed = gv.message_allowed();

		// rebroadcast not allowed so soon after GossipValidator creation
		assert!(!allowed(&sender, intent, &topic, &mut encoded_vote));

		// hack the inner deadline to be `now`
		*gv.next_rebroadcast.lock() = Instant::now();

		// rebroadcast should be allowed now
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
	}
}
