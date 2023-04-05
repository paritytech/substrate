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

use crate::{
	communication::peers::KnownPeers,
	justification::{
		proof_block_num_and_set_id, verify_with_validator_set, BeefyVersionedFinalityProof,
	},
	keystore::BeefyKeystore,
	LOG_TARGET,
};
use sp_consensus_beefy::{
	crypto::{AuthorityId, Signature},
	ValidatorSet, ValidatorSetId, VoteMessage,
};

// Timeout for rebroadcasting messages.
#[cfg(not(test))]
const REBROADCAST_AFTER: Duration = Duration::from_secs(60);
#[cfg(test)]
const REBROADCAST_AFTER: Duration = Duration::from_secs(5);

/// BEEFY gossip message type that gets encoded and sent on the network.
#[derive(Debug, Encode, Decode)]
pub(crate) enum GossipMessage<B: Block> {
	/// BEEFY message with commitment and single signature.
	Vote(VoteMessage<NumberFor<B>, AuthorityId, Signature>),
	/// BEEFY justification with commitment and signatures.
	FinalityProof(BeefyVersionedFinalityProof<B>),
}

impl<B: Block> GossipMessage<B> {
	/// Return inner vote if this message is a Vote.
	pub fn unwrap_vote(self) -> Option<VoteMessage<NumberFor<B>, AuthorityId, Signature>> {
		match self {
			GossipMessage::Vote(vote) => Some(vote),
			GossipMessage::FinalityProof(_) => None,
		}
	}

	/// Return inner finality proof if this message is a FinalityProof.
	pub fn unwrap_finality_proof(self) -> Option<BeefyVersionedFinalityProof<B>> {
		match self {
			GossipMessage::Vote(_) => None,
			GossipMessage::FinalityProof(proof) => Some(proof),
		}
	}
}

/// Gossip engine votes messages topic
pub(crate) fn votes_topic<B: Block>() -> B::Hash
where
	B: Block,
{
	<<B::Header as Header>::Hashing as Hash>::hash(b"beefy-votes")
}

/// Gossip engine justifications messages topic
pub(crate) fn proofs_topic<B: Block>() -> B::Hash
where
	B: Block,
{
	<<B::Header as Header>::Hashing as Hash>::hash(b"beefy-justifications")
}

/// A type that represents hash of the message.
pub type MessageHash = [u8; 8];

#[derive(Clone, Debug)]
pub(crate) struct GossipFilterCfg<'a, B: Block> {
	pub start: NumberFor<B>,
	pub end: NumberFor<B>,
	pub validator_set: &'a ValidatorSet<AuthorityId>,
}

#[derive(Clone, Debug)]
struct FilterInner<B: Block> {
	pub start: NumberFor<B>,
	pub end: NumberFor<B>,
	pub validator_set: ValidatorSet<AuthorityId>,
}

struct Filter<B: Block> {
	inner: Option<FilterInner<B>>,
	live_votes: BTreeMap<NumberFor<B>, fnv::FnvHashSet<MessageHash>>,
}

impl<B: Block> Filter<B> {
	pub fn new() -> Self {
		Self { inner: None, live_votes: BTreeMap::new() }
	}

	/// Update filter to new `start` and `set_id`.
	fn update(&mut self, cfg: GossipFilterCfg<B>) {
		self.live_votes.retain(|&round, _| round >= cfg.start && round <= cfg.end);
		// only clone+overwrite big validator_set if set_id changed
		match self.inner.as_mut() {
			Some(f) if f.validator_set.id() == cfg.validator_set.id() => {
				f.start = cfg.start;
				f.end = cfg.end;
			},
			_ =>
				self.inner = Some(FilterInner {
					start: cfg.start,
					end: cfg.end,
					validator_set: cfg.validator_set.clone(),
				}),
		}
	}

	/// Return true if `max(session_start, best_beefy) <= round <= best_grandpa`,
	/// and vote `set_id` matches session set id.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn is_vote_accepted(&self, round: NumberFor<B>, set_id: ValidatorSetId) -> bool {
		self.inner
			.as_ref()
			.map(|f| set_id == f.validator_set.id() && round >= f.start && round <= f.end)
			.unwrap_or(false)
	}

	/// Return true if `round` is >= than `max(session_start, best_beefy)`,
	/// and proof `set_id` matches session set id.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn is_finality_proof_accepted(&self, round: NumberFor<B>, set_id: ValidatorSetId) -> bool {
		self.inner
			.as_ref()
			.map(|f| set_id == f.validator_set.id() && round >= f.start)
			.unwrap_or(false)
	}

	/// Add new _known_ `hash` to the round's known votes.
	fn add_known_vote(&mut self, round: NumberFor<B>, hash: MessageHash) {
		self.live_votes.entry(round).or_default().insert(hash);
	}

	/// Check if `hash` is already part of round's known votes.
	fn is_known_vote(&self, round: NumberFor<B>, hash: &MessageHash) -> bool {
		self.live_votes.get(&round).map(|known| known.contains(hash)).unwrap_or(false)
	}

	fn validator_set(&self) -> Option<&ValidatorSet<AuthorityId>> {
		self.inner.as_ref().map(|f| &f.validator_set)
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
	votes_topic: B::Hash,
	justifs_topic: B::Hash,
	gossip_filter: RwLock<Filter<B>>,
	next_rebroadcast: Mutex<Instant>,
	known_peers: Arc<Mutex<KnownPeers<B>>>,
}

impl<B> GossipValidator<B>
where
	B: Block,
{
	pub fn new(known_peers: Arc<Mutex<KnownPeers<B>>>) -> GossipValidator<B> {
		GossipValidator {
			votes_topic: votes_topic::<B>(),
			justifs_topic: proofs_topic::<B>(),
			gossip_filter: RwLock::new(Filter::new()),
			next_rebroadcast: Mutex::new(Instant::now() + REBROADCAST_AFTER),
			known_peers,
		}
	}

	/// Update gossip validator filter.
	///
	/// Only votes for `set_id` and rounds `start <= round <= end` will be accepted.
	pub(crate) fn update_filter(&self, filter: GossipFilterCfg<B>) {
		debug!(target: LOG_TARGET, "🥩 New gossip filter {:?}", filter);
		self.gossip_filter.write().update(filter);
	}

	fn validate_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
		sender: &PeerId,
		data: &[u8],
	) -> ValidationResult<B::Hash> {
		let msg_hash = twox_64(data);
		let round = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		self.known_peers.lock().note_vote_for(*sender, round);

		// Verify general usefulness of the message.
		// We are going to discard old votes right away (without verification)
		// Also we keep track of already received votes to avoid verifying duplicates.
		{
			let filter = self.gossip_filter.read();

			if !filter.is_vote_accepted(round, set_id) {
				return ValidationResult::Discard
			}

			if filter.is_known_vote(round, &msg_hash) {
				return ValidationResult::ProcessAndKeep(self.votes_topic)
			}
		}

		if BeefyKeystore::verify(&vote.id, &vote.signature, &vote.commitment.encode()) {
			self.gossip_filter.write().add_known_vote(round, msg_hash);
			ValidationResult::ProcessAndKeep(self.votes_topic)
		} else {
			// TODO: report peer
			debug!(
				target: LOG_TARGET,
				"🥩 Bad signature on message: {:?}, from: {:?}", vote, sender
			);
			ValidationResult::Discard
		}
	}

	fn validate_finality_proof(
		&self,
		proof: BeefyVersionedFinalityProof<B>,
		sender: &PeerId,
	) -> ValidationResult<B::Hash> {
		let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
		self.known_peers.lock().note_vote_for(*sender, round);

		let guard = self.gossip_filter.read();
		// Verify general usefulness of the justifications.
		if !guard.is_finality_proof_accepted(round, set_id) {
			return ValidationResult::Discard
		}
		// Verify justification signatures.
		guard
			.validator_set()
			.map(|validator_set| {
				if let Ok(()) = verify_with_validator_set::<B>(round, validator_set, &proof) {
					ValidationResult::ProcessAndKeep(self.justifs_topic)
				} else {
					// TODO: report peer
					debug!(
						target: LOG_TARGET,
						"🥩 Bad signatures on message: {:?}, from: {:?}", proof, sender
					);
					ValidationResult::Discard
				}
			})
			.unwrap_or(ValidationResult::Discard)
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
		match GossipMessage::<B>::decode(&mut data) {
			Ok(GossipMessage::Vote(msg)) => self.validate_vote(msg, sender, data),
			Ok(GossipMessage::FinalityProof(proof)) => self.validate_finality_proof(proof, sender),
			Err(e) => {
				debug!(target: LOG_TARGET, "Error decoding message: {}", e);
				ValidationResult::Discard
			},
		}
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		let filter = self.gossip_filter.read();
		Box::new(move |_topic, mut data| match GossipMessage::<B>::decode(&mut data) {
			Ok(GossipMessage::Vote(msg)) => {
				let round = msg.commitment.block_number;
				let set_id = msg.commitment.validator_set_id;
				let expired = !filter.is_vote_accepted(round, set_id);
				trace!(target: LOG_TARGET, "🥩 Vote for round #{} expired: {}", round, expired);
				expired
			},
			Ok(GossipMessage::FinalityProof(proof)) => {
				let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
				let expired = !filter.is_finality_proof_accepted(round, set_id);
				trace!(
					target: LOG_TARGET,
					"🥩 Finality proof for round #{} expired: {}",
					round,
					expired
				);
				expired
			},
			Err(_) => true,
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

		let filter = self.gossip_filter.read();
		Box::new(move |_who, intent, _topic, mut data| {
			if let MessageIntent::PeriodicRebroadcast = intent {
				return do_rebroadcast
			}

			match GossipMessage::<B>::decode(&mut data) {
				Ok(GossipMessage::Vote(msg)) => {
					let round = msg.commitment.block_number;
					let set_id = msg.commitment.validator_set_id;
					let allowed = filter.is_vote_accepted(round, set_id);
					trace!(target: LOG_TARGET, "🥩 Vote for round #{} allowed: {}", round, allowed);
					allowed
				},
				Ok(GossipMessage::FinalityProof(proof)) => {
					let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
					let allowed = filter.is_finality_proof_accepted(round, set_id);
					trace!(
						target: LOG_TARGET,
						"🥩 Finality proof for round #{} allowed: {}",
						round,
						allowed
					);
					allowed
				},
				Err(_) => false,
			}
		})
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::keystore::BeefyKeystore;
	use sc_network_test::Block;
	use sp_consensus_beefy::{
		crypto::Signature, known_payloads, Commitment, Keyring, MmrRootHash, Payload,
		SignedCommitment, VoteMessage, KEY_TYPE,
	};
	use sp_keystore::{testing::MemoryKeystore, Keystore};

	#[test]
	fn known_votes_insert_remove() {
		let mut filter = Filter::<Block>::new();
		let msg_hash = twox_64(b"data");
		let keys = vec![Keyring::Alice.public()];
		let validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 1).unwrap();

		filter.add_known_vote(1, msg_hash);
		filter.add_known_vote(1, msg_hash);
		filter.add_known_vote(2, msg_hash);
		assert_eq!(filter.live_votes.len(), 2);

		filter.add_known_vote(3, msg_hash);
		assert!(filter.is_known_vote(3, &msg_hash));
		assert!(!filter.is_known_vote(3, &twox_64(b"other")));
		assert!(!filter.is_known_vote(4, &msg_hash));
		assert_eq!(filter.live_votes.len(), 3);

		assert!(filter.inner.is_none());
		assert!(!filter.is_vote_accepted(1, 1));

		filter.update(GossipFilterCfg { start: 3, end: 10, validator_set: &validator_set });
		assert_eq!(filter.live_votes.len(), 1);
		assert!(filter.live_votes.contains_key(&3));
		assert!(!filter.is_vote_accepted(2, 1));
		assert!(filter.is_vote_accepted(3, 1));
		assert!(filter.is_vote_accepted(4, 1));
		assert!(!filter.is_vote_accepted(4, 2));

		let validator_set = ValidatorSet::<AuthorityId>::new(keys, 2).unwrap();
		filter.update(GossipFilterCfg { start: 5, end: 10, validator_set: &validator_set });
		assert!(filter.live_votes.is_empty());
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

	pub fn sign_commitment<BN: Encode>(who: &Keyring, commitment: &Commitment<BN>) -> Signature {
		let store = MemoryKeystore::new();
		store.ecdsa_generate_new(KEY_TYPE, Some(&who.to_seed())).unwrap();
		let beefy_keystore: BeefyKeystore = Some(store.into()).into();
		beefy_keystore.sign(&who.public(), &commitment.encode()).unwrap()
	}

	fn dummy_vote(block_number: u64) -> VoteMessage<u64, AuthorityId, Signature> {
		let payload = Payload::from_single_entry(
			known_payloads::MMR_ROOT_ID,
			MmrRootHash::default().encode(),
		);
		let commitment = Commitment { payload, block_number, validator_set_id: 0 };
		let signature = sign_commitment(&Keyring::Alice, &commitment);

		VoteMessage { commitment, id: Keyring::Alice.public(), signature }
	}

	pub fn dummy_proof(
		block_number: u64,
		validator_set: &ValidatorSet<AuthorityId>,
	) -> BeefyVersionedFinalityProof<Block> {
		let payload = Payload::from_single_entry(
			known_payloads::MMR_ROOT_ID,
			MmrRootHash::default().encode(),
		);
		let commitment = Commitment { payload, block_number, validator_set_id: validator_set.id() };
		let signatures = validator_set
			.validators()
			.iter()
			.map(|validator: &AuthorityId| {
				Some(sign_commitment(&Keyring::from_public(validator).unwrap(), &commitment))
			})
			.collect();

		BeefyVersionedFinalityProof::<Block>::V1(SignedCommitment { commitment, signatures })
	}

	#[test]
	fn should_validate_messages() {
		let keys = vec![Keyring::Alice.public()];
		let validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 0).unwrap();
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		gv.update_filter(GossipFilterCfg { start: 0, end: 10, validator_set: &validator_set });
		let sender = sc_network::PeerId::random();
		let mut context = TestContext;

		let vote = dummy_vote(3);
		let gossip_vote = GossipMessage::<Block>::Vote(vote.clone());

		// first time the cache should be populated
		let res = gv.validate(&mut context, &sender, &gossip_vote.encode());

		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		assert_eq!(
			gv.gossip_filter
				.read()
				.live_votes
				.get(&vote.commitment.block_number)
				.map(|x| x.len()),
			Some(1)
		);

		// second time we should hit the cache
		let res = gv.validate(&mut context, &sender, &gossip_vote.encode());
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// next we should quickly reject if the round is not live
		gv.update_filter(GossipFilterCfg { start: 7, end: 10, validator_set: &validator_set });

		let number = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		assert!(!gv.gossip_filter.read().is_vote_accepted(number, set_id));

		let res = gv.validate(&mut context, &sender, &vote.encode());
		assert!(matches!(res, ValidationResult::Discard));

		// reject old proof
		let proof = dummy_proof(5, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));

		// accept next proof with good set_id
		let proof = dummy_proof(7, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// accept future proof with good set_id
		let proof = dummy_proof(20, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

		// reject proof, wrong set_id
		let bad_validator_set = ValidatorSet::<AuthorityId>::new(keys, 1).unwrap();
		let proof = dummy_proof(20, &bad_validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));

		// reject proof, bad signatures (Bob instead of Alice)
		let bad_validator_set =
			ValidatorSet::<AuthorityId>::new(vec![Keyring::Bob.public()], 0).unwrap();
		let proof = dummy_proof(20, &bad_validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));
	}

	#[test]
	fn messages_allowed_and_expired() {
		let keys = vec![Keyring::Alice.public()];
		let validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 0).unwrap();
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		gv.update_filter(GossipFilterCfg { start: 0, end: 10, validator_set: &validator_set });
		let sender = sc_network::PeerId::random();
		let topic = Default::default();
		let intent = MessageIntent::Broadcast;

		// conclude 2
		gv.update_filter(GossipFilterCfg { start: 2, end: 10, validator_set: &validator_set });
		let mut allowed = gv.message_allowed();
		let mut expired = gv.message_expired();

		// check bad vote format
		assert!(!allowed(&sender, intent, &topic, &mut [0u8; 16]));
		assert!(expired(topic, &mut [0u8; 16]));

		// inactive round 1 -> expired
		let vote = dummy_vote(1);
		let mut encoded_vote = GossipMessage::<Block>::Vote(vote).encode();
		assert!(!allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(expired(topic, &mut encoded_vote));
		let proof = dummy_proof(1, &validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(!allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(expired(topic, &mut encoded_proof));

		// active round 2 -> !expired - concluded but still gossiped
		let vote = dummy_vote(2);
		let mut encoded_vote = GossipMessage::<Block>::Vote(vote).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));
		let proof = dummy_proof(2, &validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(!expired(topic, &mut encoded_proof));
		// using wrong set_id -> !allowed, expired
		let bad_validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 1).unwrap();
		let proof = dummy_proof(2, &bad_validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(!allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(expired(topic, &mut encoded_proof));

		// in progress round 3 -> !expired
		let vote = dummy_vote(3);
		let mut encoded_vote = GossipMessage::<Block>::Vote(vote).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));
		let proof = dummy_proof(3, &validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(!expired(topic, &mut encoded_proof));

		// unseen round 4 -> !expired
		let vote = dummy_vote(4);
		let mut encoded_vote = GossipMessage::<Block>::Vote(vote).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(!expired(topic, &mut encoded_vote));
		let proof = dummy_proof(4, &validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(!expired(topic, &mut encoded_proof));

		// future round 11 -> expired
		let vote = dummy_vote(11);
		let mut encoded_vote = GossipMessage::<Block>::Vote(vote).encode();
		assert!(!allowed(&sender, intent, &topic, &mut encoded_vote));
		assert!(expired(topic, &mut encoded_vote));
		// future proofs allowed while same set_id -> allowed
		let proof = dummy_proof(11, &validator_set);
		let mut encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		assert!(allowed(&sender, intent, &topic, &mut encoded_proof));
		assert!(!expired(topic, &mut encoded_proof));
	}

	#[test]
	fn messages_rebroadcast() {
		let keys = vec![Keyring::Alice.public()];
		let validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 0).unwrap();
		let gv = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		gv.update_filter(GossipFilterCfg { start: 0, end: 10, validator_set: &validator_set });
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
