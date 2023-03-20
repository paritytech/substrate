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
use sp_consensus_beefy::{
	crypto::{Public, Signature},
	ValidatorSetId, VoteMessage,
};

// Timeout for rebroadcasting messages.
#[cfg(not(test))]
const REBROADCAST_AFTER: Duration = Duration::from_secs(60);
#[cfg(test)]
const REBROADCAST_AFTER: Duration = Duration::from_secs(5);

/// Gossip engine messages topic
pub(crate) fn topic<B: Block>() -> B::Hash
where
	B: Block,
{
	<<B::Header as Header>::Hashing as Hash>::hash(b"beefy")
}

#[derive(Debug)]
pub(crate) struct GossipVoteFilter<B: Block> {
	pub start: NumberFor<B>,
	pub end: NumberFor<B>,
	pub validator_set_id: ValidatorSetId,
}

/// A type that represents hash of the message.
pub type MessageHash = [u8; 8];

struct VotesFilter<B: Block> {
	filter: Option<GossipVoteFilter<B>>,
	live: BTreeMap<NumberFor<B>, fnv::FnvHashSet<MessageHash>>,
}

impl<B: Block> VotesFilter<B> {
	pub fn new() -> Self {
		Self { filter: None, live: BTreeMap::new() }
	}

	/// Update filter to new `start` and `set_id`.
	fn update(&mut self, filter: GossipVoteFilter<B>) {
		self.live.retain(|&round, _| round >= filter.start && round <= filter.end);
		self.filter = Some(filter);
	}

	/// Return true if `round` is >= than `max(session_start, best_beefy)`,
	/// and vote set id matches session set id.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn is_live(&self, round: NumberFor<B>, set_id: ValidatorSetId) -> bool {
		self.filter
			.as_ref()
			.map(|f| set_id == f.validator_set_id && round >= f.start && round <= f.end)
			.unwrap_or(false)
	}

	/// Add new _known_ `hash` to the round's known votes.
	fn add_known(&mut self, round: NumberFor<B>, hash: MessageHash) {
		self.live.entry(round).or_default().insert(hash);
	}

	/// Check if `hash` is already part of round's known votes.
	fn is_known(&self, round: NumberFor<B>, hash: &MessageHash) -> bool {
		self.live.get(&round).map(|known| known.contains(hash)).unwrap_or(false)
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
	votes_filter: RwLock<VotesFilter<B>>,
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
			votes_filter: RwLock::new(VotesFilter::new()),
			next_rebroadcast: Mutex::new(Instant::now() + REBROADCAST_AFTER),
			known_peers,
		}
	}

	/// Update gossip validator filter.
	///
	/// Only votes for `set_id` and rounds `start <= round <= end` will be accepted.
	pub(crate) fn update_filter(&self, filter: GossipVoteFilter<B>) {
		debug!(target: LOG_TARGET, "🥩 New gossip filter {:?}", filter);
		self.votes_filter.write().update(filter);
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
			let set_id = msg.commitment.validator_set_id;
			self.known_peers.lock().note_vote_for(*sender, round);

			// Verify general usefulness of the message.
			// We are going to discard old votes right away (without verification)
			// Also we keep track of already received votes to avoid verifying duplicates.
			{
				let filter = self.votes_filter.read();

				if !filter.is_live(round, set_id) {
					return ValidationResult::Discard
				}

				if filter.is_known(round, &msg_hash) {
					return ValidationResult::ProcessAndKeep(self.topic)
				}
			}

			if BeefyKeystore::verify(&msg.id, &msg.signature, &msg.commitment.encode()) {
				self.votes_filter.write().add_known(round, msg_hash);
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
		let filter = self.votes_filter.read();
		Box::new(move |_topic, mut data| {
			let msg = match VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return true,
			};

			let round = msg.commitment.block_number;
			let set_id = msg.commitment.validator_set_id;
			let expired = !filter.is_live(round, set_id);

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
				trace!(target: LOG_TARGET, "🥩 Gossip rebroadcast");
				*next_rebroadcast = now + REBROADCAST_AFTER;
				true
			} else {
				false
			}
		};

		let filter = self.votes_filter.read();
		Box::new(move |_who, intent, _topic, mut data| {
			if let MessageIntent::PeriodicRebroadcast = intent {
				return do_rebroadcast
			}

			let msg = match VoteMessage::<NumberFor<B>, Public, Signature>::decode(&mut data) {
				Ok(vote) => vote,
				Err(_) => return false,
			};

			let round = msg.commitment.block_number;
			let set_id = msg.commitment.validator_set_id;
			let allowed = filter.is_live(round, set_id);

			trace!(target: LOG_TARGET, "🥩 Message for round #{} allowed: {}", round, allowed);

			allowed
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::keystore::BeefyKeystore;
	use sc_network_test::Block;
	use sp_consensus_beefy::{
		crypto::Signature, known_payloads, Commitment, Keyring, MmrRootHash, Payload, VoteMessage,
		KEY_TYPE,
	};
	use sp_keystore::{testing::MemoryKeystore, Keystore};

	#[test]
	fn known_votes_insert_remove() {
		let mut kv = VotesFilter::<Block>::new();
		let msg_hash = twox_64(b"data");

		kv.add_known(1, msg_hash);
		kv.add_known(1, msg_hash);
		kv.add_known(2, msg_hash);
		assert_eq!(kv.live.len(), 2);

		kv.add_known(3, msg_hash);
		assert!(kv.is_known(3, &msg_hash));
		assert!(!kv.is_known(3, &twox_64(b"other")));
		assert!(!kv.is_known(4, &msg_hash));
		assert_eq!(kv.live.len(), 3);

		assert!(kv.filter.is_none());
		assert!(!kv.is_live(1, 1));

		kv.update(GossipVoteFilter { start: 3, end: 10, validator_set_id: 1 });
		assert_eq!(kv.live.len(), 1);
		assert!(kv.live.contains_key(&3));
		assert!(!kv.is_live(2, 1));
		assert!(kv.is_live(3, 1));
		assert!(kv.is_live(4, 1));
		assert!(!kv.is_live(4, 2));

		kv.update(GossipVoteFilter { start: 5, end: 10, validator_set_id: 2 });
		assert!(kv.live.is_empty());
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
		let store = MemoryKeystore::new();
		store.ecdsa_generate_new(KEY_TYPE, Some(&who.to_seed())).unwrap();
		let beefy_keystore: BeefyKeystore = Some(store.into()).into();
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
		gv.update_filter(GossipVoteFilter { start: 0, end: 10, validator_set_id: 0 });
		let sender = sc_network::PeerId::random();
		let mut context = TestContext;

		let vote = dummy_vote(3);

		// first time the cache should be populated
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		assert_eq!(
			gv.votes_filter.read().live.get(&vote.commitment.block_number).map(|x| x.len()),
			Some(1)
		);

		// second time we should hit the cache
		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// next we should quickly reject if the round is not live
		gv.update_filter(GossipVoteFilter { start: 7, end: 10, validator_set_id: 0 });

		let number = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		assert!(!gv.votes_filter.read().is_live(number, set_id));

		let res = gv.validate(&mut context, &sender, &vote.encode());

		assert!(matches!(res, ValidationResult::Discard));
	}

	#[test]
	fn messages_allowed_and_expired() {
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		gv.update_filter(GossipVoteFilter { start: 0, end: 10, validator_set_id: 0 });
		let sender = sc_network::PeerId::random();
		let topic = Default::default();
		let intent = MessageIntent::Broadcast;

		// conclude 2
		gv.update_filter(GossipVoteFilter { start: 2, end: 10, validator_set_id: 0 });
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
		gv.update_filter(GossipVoteFilter { start: 0, end: 10, validator_set_id: 0 });
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
