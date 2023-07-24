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

use sc_network::{PeerId, ReputationChange};
use sc_network_gossip::{MessageIntent, ValidationResult, Validator, ValidatorContext};
use sp_core::hashing::twox_64;
use sp_runtime::traits::{Block, Hash, Header, NumberFor};

use codec::{Decode, DecodeAll, Encode};
use log::{debug, trace};
use parking_lot::{Mutex, RwLock};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use wasm_timer::Instant;

use crate::{
	communication::{
		benefit, cost,
		peers::{KnownPeers, PeerReport},
	},
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

#[derive(Debug, PartialEq)]
pub(super) enum Action<H> {
	// repropagate under given topic, to the given peers, applying cost/benefit to originator.
	Keep(H, ReputationChange),
	// discard, applying cost/benefit to originator.
	Discard(ReputationChange),
}

/// An outcome of examining a message.
#[derive(Debug, PartialEq, Clone, Copy)]
enum Consider {
	/// Accept the message.
	Accept,
	/// Message is too early. Reject.
	RejectPast,
	/// Message is from the future. Reject.
	RejectFuture,
	/// Message cannot be evaluated. Reject.
	RejectOutOfScope,
}

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

	/// Accept if `max(session_start, best_beefy) <= round <= best_grandpa`,
	/// and vote `set_id` matches session set id.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn consider_vote(&self, round: NumberFor<B>, set_id: ValidatorSetId) -> Consider {
		self.inner
			.as_ref()
			.map(|f|
				// only from current set and only [filter.start, filter.end]
				if set_id < f.validator_set.id() {
					Consider::RejectPast
				} else if set_id > f.validator_set.id() {
					Consider::RejectFuture
				} else if round < f.start {
					Consider::RejectPast
				} else if round > f.end {
					Consider::RejectFuture
				} else {
					Consider::Accept
				})
			.unwrap_or(Consider::RejectOutOfScope)
	}

	/// Return true if `round` is >= than `max(session_start, best_beefy)`,
	/// and proof `set_id` matches session set id.
	///
	/// Latest concluded round is still considered alive to allow proper gossiping for it.
	fn consider_finality_proof(&self, round: NumberFor<B>, set_id: ValidatorSetId) -> Consider {
		self.inner
			.as_ref()
			.map(|f|
				// only from current set and only >= filter.start
				if round < f.start || set_id < f.validator_set.id() {
					Consider::RejectPast
				} else if set_id > f.validator_set.id() {
					Consider::RejectFuture
				} else {
					Consider::Accept
				}
			)
			.unwrap_or(Consider::RejectOutOfScope)
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
	report_sender: TracingUnboundedSender<PeerReport>,
}

impl<B> GossipValidator<B>
where
	B: Block,
{
	pub(crate) fn new(
		known_peers: Arc<Mutex<KnownPeers<B>>>,
	) -> (GossipValidator<B>, TracingUnboundedReceiver<PeerReport>) {
		let (tx, rx) = tracing_unbounded("mpsc_beefy_gossip_validator", 10_000);
		let val = GossipValidator {
			votes_topic: votes_topic::<B>(),
			justifs_topic: proofs_topic::<B>(),
			gossip_filter: RwLock::new(Filter::new()),
			next_rebroadcast: Mutex::new(Instant::now() + REBROADCAST_AFTER),
			known_peers,
			report_sender: tx,
		};
		(val, rx)
	}

	/// Update gossip validator filter.
	///
	/// Only votes for `set_id` and rounds `start <= round <= end` will be accepted.
	pub(crate) fn update_filter(&self, filter: GossipFilterCfg<B>) {
		debug!(target: LOG_TARGET, "🥩 New gossip filter {:?}", filter);
		self.gossip_filter.write().update(filter);
	}

	fn report(&self, who: PeerId, cost_benefit: ReputationChange) {
		let _ = self.report_sender.unbounded_send(PeerReport { who, cost_benefit });
	}

	fn validate_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
		sender: &PeerId,
		data: &[u8],
	) -> Action<B::Hash> {
		let msg_hash = twox_64(data);
		let round = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		self.known_peers.lock().note_vote_for(*sender, round);

		// Verify general usefulness of the message.
		// We are going to discard old votes right away (without verification)
		// Also we keep track of already received votes to avoid verifying duplicates.
		{
			let filter = self.gossip_filter.read();

			match filter.consider_vote(round, set_id) {
				Consider::RejectPast => return Action::Discard(cost::OUTDATED_MESSAGE),
				Consider::RejectFuture => return Action::Discard(cost::FUTURE_MESSAGE),
				Consider::RejectOutOfScope => return Action::Discard(cost::OUT_OF_SCOPE_MESSAGE),
				Consider::Accept => {},
			}

			if filter.is_known_vote(round, &msg_hash) {
				return Action::Keep(self.votes_topic, benefit::KNOWN_VOTE_MESSAGE)
			}

			// ensure authority is part of the set.
			if !filter
				.validator_set()
				.map(|set| set.validators().contains(&vote.id))
				.unwrap_or(false)
			{
				debug!(target: LOG_TARGET, "Message from voter not in validator set: {}", vote.id);
				return Action::Discard(cost::UNKNOWN_VOTER)
			}
		}

		if BeefyKeystore::verify(&vote.id, &vote.signature, &vote.commitment.encode()) {
			self.gossip_filter.write().add_known_vote(round, msg_hash);
			Action::Keep(self.votes_topic, benefit::VOTE_MESSAGE)
		} else {
			debug!(
				target: LOG_TARGET,
				"🥩 Bad signature on message: {:?}, from: {:?}", vote, sender
			);
			Action::Discard(cost::BAD_SIGNATURE)
		}
	}

	fn validate_finality_proof(
		&self,
		proof: BeefyVersionedFinalityProof<B>,
		sender: &PeerId,
	) -> Action<B::Hash> {
		let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
		self.known_peers.lock().note_vote_for(*sender, round);

		let guard = self.gossip_filter.read();
		// Verify general usefulness of the justification.
		match guard.consider_finality_proof(round, set_id) {
			Consider::RejectPast => return Action::Discard(cost::OUTDATED_MESSAGE),
			Consider::RejectFuture => return Action::Discard(cost::FUTURE_MESSAGE),
			Consider::RejectOutOfScope => return Action::Discard(cost::OUT_OF_SCOPE_MESSAGE),
			Consider::Accept => {},
		}
		// Verify justification signatures.
		guard
			.validator_set()
			.map(|validator_set| {
				if let Err((_, signatures_checked)) =
					verify_with_validator_set::<B>(round, validator_set, &proof)
				{
					debug!(
						target: LOG_TARGET,
						"🥩 Bad signatures on message: {:?}, from: {:?}", proof, sender
					);
					let mut cost = cost::INVALID_PROOF;
					cost.value +=
						cost::PER_SIGNATURE_CHECKED.saturating_mul(signatures_checked as i32);
					Action::Discard(cost)
				} else {
					Action::Keep(self.justifs_topic, benefit::VALIDATED_PROOF)
				}
			})
			.unwrap_or(Action::Discard(cost::OUT_OF_SCOPE_MESSAGE))
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
		context: &mut dyn ValidatorContext<B>,
		sender: &PeerId,
		mut data: &[u8],
	) -> ValidationResult<B::Hash> {
		let raw = data;
		let action = match GossipMessage::<B>::decode_all(&mut data) {
			Ok(GossipMessage::Vote(msg)) => self.validate_vote(msg, sender, raw),
			Ok(GossipMessage::FinalityProof(proof)) => self.validate_finality_proof(proof, sender),
			Err(e) => {
				debug!(target: LOG_TARGET, "Error decoding message: {}", e);
				let bytes = raw.len().min(i32::MAX as usize) as i32;
				let cost = ReputationChange::new(
					bytes.saturating_mul(cost::PER_UNDECODABLE_BYTE),
					"BEEFY: Bad packet",
				);
				Action::Discard(cost)
			},
		};
		match action {
			Action::Keep(topic, cb) => {
				self.report(*sender, cb);
				context.broadcast_message(topic, data.to_vec(), false);
				ValidationResult::ProcessAndKeep(topic)
			},
			Action::Discard(cb) => {
				self.report(*sender, cb);
				ValidationResult::Discard
			},
		}
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(B::Hash, &[u8]) -> bool + 'a> {
		let filter = self.gossip_filter.read();
		Box::new(move |_topic, mut data| match GossipMessage::<B>::decode_all(&mut data) {
			Ok(GossipMessage::Vote(msg)) => {
				let round = msg.commitment.block_number;
				let set_id = msg.commitment.validator_set_id;
				let expired = filter.consider_vote(round, set_id) != Consider::Accept;
				trace!(target: LOG_TARGET, "🥩 Vote for round #{} expired: {}", round, expired);
				expired
			},
			Ok(GossipMessage::FinalityProof(proof)) => {
				let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
				let expired = filter.consider_finality_proof(round, set_id) != Consider::Accept;
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

			match GossipMessage::<B>::decode_all(&mut data) {
				Ok(GossipMessage::Vote(msg)) => {
					let round = msg.commitment.block_number;
					let set_id = msg.commitment.validator_set_id;
					let allowed = filter.consider_vote(round, set_id) == Consider::Accept;
					trace!(target: LOG_TARGET, "🥩 Vote for round #{} allowed: {}", round, allowed);
					allowed
				},
				Ok(GossipMessage::FinalityProof(proof)) => {
					let (round, set_id) = proof_block_num_and_set_id::<B>(&proof);
					let allowed = filter.consider_finality_proof(round, set_id) == Consider::Accept;
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
		assert_eq!(filter.consider_vote(1, 1), Consider::RejectOutOfScope);

		filter.update(GossipFilterCfg { start: 3, end: 10, validator_set: &validator_set });
		assert_eq!(filter.live_votes.len(), 1);
		assert!(filter.live_votes.contains_key(&3));
		assert_eq!(filter.consider_vote(2, 1), Consider::RejectPast);
		assert_eq!(filter.consider_vote(3, 1), Consider::Accept);
		assert_eq!(filter.consider_vote(4, 1), Consider::Accept);
		assert_eq!(filter.consider_vote(20, 1), Consider::RejectFuture);
		assert_eq!(filter.consider_vote(4, 2), Consider::RejectFuture);

		let validator_set = ValidatorSet::<AuthorityId>::new(keys, 2).unwrap();
		filter.update(GossipFilterCfg { start: 5, end: 10, validator_set: &validator_set });
		assert!(filter.live_votes.is_empty());
	}

	struct TestContext;
	impl<B: sp_runtime::traits::Block> ValidatorContext<B> for TestContext {
		fn broadcast_topic(&mut self, _topic: B::Hash, _force: bool) {
			todo!()
		}

		fn broadcast_message(&mut self, _topic: B::Hash, _message: Vec<u8>, _force: bool) {}

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
		let (gv, mut report_stream) =
			GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
		let sender = PeerId::random();
		let mut context = TestContext;

		// reject message, decoding error
		let bad_encoding = b"0000000000".as_slice();
		let expected_cost = ReputationChange::new(
			(bad_encoding.len() as i32).saturating_mul(cost::PER_UNDECODABLE_BYTE),
			"BEEFY: Bad packet",
		);
		let mut expected_report = PeerReport { who: sender, cost_benefit: expected_cost };
		let res = gv.validate(&mut context, &sender, bad_encoding);
		assert!(matches!(res, ValidationResult::Discard));
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// verify votes validation

		let vote = dummy_vote(3);
		let encoded = GossipMessage::<Block>::Vote(vote.clone()).encode();

		// filter not initialized
		let res = gv.validate(&mut context, &sender, &encoded);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::OUT_OF_SCOPE_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		gv.update_filter(GossipFilterCfg { start: 0, end: 10, validator_set: &validator_set });
		// nothing in cache first time
		let res = gv.validate(&mut context, &sender, &encoded);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		expected_report.cost_benefit = benefit::VOTE_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);
		assert_eq!(
			gv.gossip_filter
				.read()
				.live_votes
				.get(&vote.commitment.block_number)
				.map(|x| x.len()),
			Some(1)
		);

		// second time we should hit the cache
		let res = gv.validate(&mut context, &sender, &encoded);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		expected_report.cost_benefit = benefit::KNOWN_VOTE_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// reject vote, voter not in validator set
		let mut bad_vote = vote.clone();
		bad_vote.id = Keyring::Bob.public();
		let bad_vote = GossipMessage::<Block>::Vote(bad_vote).encode();
		let res = gv.validate(&mut context, &sender, &bad_vote);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::UNKNOWN_VOTER;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// reject if the round is not GRANDPA finalized
		gv.update_filter(GossipFilterCfg { start: 1, end: 2, validator_set: &validator_set });
		let number = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		assert_eq!(gv.gossip_filter.read().consider_vote(number, set_id), Consider::RejectFuture);
		let res = gv.validate(&mut context, &sender, &encoded);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::FUTURE_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// reject if the round is not live anymore
		gv.update_filter(GossipFilterCfg { start: 7, end: 10, validator_set: &validator_set });
		let number = vote.commitment.block_number;
		let set_id = vote.commitment.validator_set_id;
		assert_eq!(gv.gossip_filter.read().consider_vote(number, set_id), Consider::RejectPast);
		let res = gv.validate(&mut context, &sender, &encoded);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::OUTDATED_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// now verify proofs validation

		// reject old proof
		let proof = dummy_proof(5, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::OUTDATED_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// accept next proof with good set_id
		let proof = dummy_proof(7, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		expected_report.cost_benefit = benefit::VALIDATED_PROOF;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// accept future proof with good set_id
		let proof = dummy_proof(20, &validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
		expected_report.cost_benefit = benefit::VALIDATED_PROOF;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// reject proof, future set_id
		let bad_validator_set = ValidatorSet::<AuthorityId>::new(keys, 1).unwrap();
		let proof = dummy_proof(20, &bad_validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::FUTURE_MESSAGE;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);

		// reject proof, bad signatures (Bob instead of Alice)
		let bad_validator_set =
			ValidatorSet::<AuthorityId>::new(vec![Keyring::Bob.public()], 0).unwrap();
		let proof = dummy_proof(20, &bad_validator_set);
		let encoded_proof = GossipMessage::<Block>::FinalityProof(proof).encode();
		let res = gv.validate(&mut context, &sender, &encoded_proof);
		assert!(matches!(res, ValidationResult::Discard));
		expected_report.cost_benefit = cost::INVALID_PROOF;
		expected_report.cost_benefit.value += cost::PER_SIGNATURE_CHECKED;
		assert_eq!(report_stream.try_recv().unwrap(), expected_report);
	}

	#[test]
	fn messages_allowed_and_expired() {
		let keys = vec![Keyring::Alice.public()];
		let validator_set = ValidatorSet::<AuthorityId>::new(keys.clone(), 0).unwrap();
		let (gv, _) = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
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
		let (gv, _) = GossipValidator::<Block>::new(Arc::new(Mutex::new(KnownPeers::new())));
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
