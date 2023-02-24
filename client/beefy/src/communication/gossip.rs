// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use std::{collections::BTreeMap, sync::Arc, time::Duration};

use sc_network::PeerId;
use sc_network_gossip::{MessageIntent, ValidationResult, Validator, ValidatorContext};
use sp_core::hashing::twox_64;
use sp_runtime::traits::{Block, Hash, Header, NumberFor};

use codec::{Decode, Encode};
use log::{debug, trace};
use parking_lot::{Mutex, RwLock};
use wasm_timer::Instant;

use crate::{communication::peers::KnownPeers, keystore::BeefyKeystore, LOG_TARGET};
use beefy_primitives::{
	crypto::{Public, Signature},
	VoteMessage,
};

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
	fn insert(&mut self, round: NumberFor<B>) {
		self.live.entry(round).or_default();
	}

	/// Remove `round` and older from live set, update `last_done` accordingly.
	fn conclude(&mut self, round: NumberFor<B>) {
		self.live.retain(|&number, _| number > round);
		self.last_done = self.last_done.max(Some(round));
	}

	/// Return true if `round` is newer than previously concluded rounds.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn is_live(&self, round: &NumberFor<B>) -> bool {
		Some(*round) >= self.last_done
	}

	/// Add new _known_ `hash` to the round's known votes.
	fn add_known(&mut self, round: &NumberFor<B>, hash: MessageHash) {
		self.live.get_mut(round).map(|known| known.insert(hash));
	}

	/// Check if `hash` is already part of round's known votes.
	fn is_known(&self, round: &NumberFor<B>, hash: &MessageHash) -> bool {
		self.live.get(round).map(|known| known.contains(hash)).unwrap_or(false)
	}
}

/// BEEFY gossip validator
///
/// Validate BEEFY gossip messages and limit the number of live BEEFY voting rounds.
///
/// Allows messages for 'rounds >= last concluded' to flow, everything else gets
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
	known_peers: Arc<Mutex<KnownPeers<B>>>,
}

impl<B> GossipValidator<B>
where
	B: Block,
{
	pub fn new(known_peers: Arc<Mutex<KnownPeers<B>>>) -> GossipValidator<B> {
		GossipValidator {
			topic: topic::<B>(),
			known_votes: RwLock::new(KnownVotes::new()),
			next_rebroadcast: Mutex::new(Instant::now() + REBROADCAST_AFTER),
			known_peers,
		}
	}

	/// Note a voting round.
	///
	/// Noting round will track gossiped votes for `round`.
	pub(crate) fn note_round(&self, round: NumberFor<B>) {
		debug!(target: LOG_TARGET, "🥩 About to note gossip round #{}", round);
		self.known_votes.write().insert(round);
	}

	/// Conclude a voting round.
	///
	/// This can be called once round is complete so we stop gossiping for it.
	pub(crate) fn conclude_round(&self, round: NumberFor<B>) {
		debug!(target: LOG_TARGET, "🥩 About to drop gossip round #{}", round);
		self.known_votes.write().conclude(round);
	}
}

impl<B> Validator<B> for GossipValidator<B>
where
	B: Block,
{
	fn peer_disconnected(&self, _context: &mut dyn ValidatorContext<B>, who: &PeerId) {
		self.known_peers.lock().remove(who);
	}

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

				if !known_votes.is_live(&round) {
					return ValidationResult::Discard
				}

				if known_votes.is_known(&round, &msg_hash) {
					return ValidationResult::ProcessAndKeep(self.topic)
				}
			}

			if BeefyKeystore::verify(&msg.id, &msg.signature, &msg.commitment.encode()) {
				self.known_votes.write().add_known(&round, msg_hash);
				self.known_peers.lock().note_vote_for(*sender, round);
				return ValidationResult::ProcessAndKeep(self.topic)
			} else {
				// TODO: report peer
				debug!(
					target: LOG_TARGET,
					"🥩 Bad signature on message: {:?}, from: {:?}", msg, sender
				);
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
			let expired = !known_votes.is_live(&round);

			trace!(target: LOG_TARGET, "🥩 Message for round #{} expired: {}", round, expired);

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

			let msg = match VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return false,
			};

			let round = msg.commitment.block_number;
			let allowed = known_votes.is_live(&round);

			trace!(target: LOG_TARGET, "🥩 Message for round #{} allowed: {}", round, allowed);

			allowed
		})
	}
}

#[cfg(test)]
mod tests {
	use sc_keystore::LocalKeystore;
	use sc_network_test::Block;
	use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

	use crate::keystore::BeefyKeystore;
	use beefy_primitives::{
		crypto::Signature, known_payloads, Commitment, Keyring, MmrRootHash, Payload, VoteMessage,
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

		let mut kv = KnownVotes::<Block>::new();
		kv.insert(1);
		kv.insert(2);
		kv.insert(3);

		assert!(kv.last_done.is_none());
		kv.conclude(2);
		assert_eq!(kv.live.len(), 1);
		assert!(!kv.live.contains_key(&2));
		assert_eq!(kv.last_done, Some(2));

		kv.conclude(1);
		assert_eq!(kv.last_done, Some(2));

		kv.conclude(3);
		assert_eq!(kv.last_done, Some(3));
		assert!(kv.live.is_empty());
	}

	#[test]
	fn note_and_drop_round_works() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));

		gv.note_round(1u64);

		assert!(gv.known_votes.read().is_live(&1u64));

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		assert_eq!(gv.known_votes.read().live.len(), 4);

		gv.conclude_round(7u64);

		let votes = gv.known_votes.read();

		// rounds 1 and 3 are outdated, don't gossip anymore
		assert!(!votes.is_live(&1u64));
		assert!(!votes.is_live(&3u64));
		// latest concluded round is still gossiped
		assert!(votes.is_live(&7u64));
		// round 10 is alive and in-progress
		assert!(votes.is_live(&10u64));
	}

	#[test]
	fn note_same_round_twice() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));

		gv.note_round(3u64);
		gv.note_round(7u64);
		gv.note_round(10u64);

		assert_eq!(gv.known_votes.read().live.len(), 3);

		// note round #7 again -> should not change anything
		gv.note_round(7u64);

		let votes = gv.known_votes.read();

		assert_eq!(votes.live.len(), 3);

		assert!(votes.is_live(&3u64));
		assert!(votes.is_live(&7u64));
		assert!(votes.is_live(&10u64));
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
		let payload = Payload::from_single_entry(
			known_payloads::MMR_ROOT_ID,
			MmrRootHash::default().encode(),
		);
		let commitment = Commitment { payload, block_number, validator_set_id: 0 };
		let signature = sign_commitment(&Keyring::Alice, &commitment);

		VoteMessage { commitment, id: Keyring::Alice.public(), signature }
	}

	#[test]
	fn should_avoid_verifying_signatures_twice() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
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
		gv.conclude_round(7_u64);

		assert!(!gv.known_votes.read().is_live(&vote.commitment.block_number));

		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::Discard));
	}

	#[test]
	fn messages_allowed_and_expired() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		let sender = sc_network::PeerId::random();
		let topic = Default::default();
		let intent = MessageIntent::Broadcast;

		// note round 2 and 3, then conclude 2
		gv.note_round(2u64);
		gv.note_round(3u64);
		gv.conclude_round(2u64);
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

		// active round 2 -> !expired - concluded but still gossiped
		let vote = dummy_vote(2);
		let mut encoded_vote = vote.encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));

		// in progress round 3 -> !expired
		let vote = dummy_vote(3);
		let mut encoded_vote = vote.encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));

		// unseen round 4 -> !expired
		let vote = dummy_vote(3);
		let mut encoded_vote = vote.encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));
	}

	#[test]
	fn messages_rebroadcast() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
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

		// still not allowed on old `allowed` closure result
		assert!(!allowed(&sender, intent, &topic, &mut encoded_vote));

		// renew closure result
		let mut allowed = gv.message_allowed();
		// rebroadcast should be allowed now
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
	}
}
