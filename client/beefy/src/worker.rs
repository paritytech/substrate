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

use std::{
	convert::{TryFrom, TryInto},
	fmt::Debug,
	marker::PhantomData,
	sync::Arc,
};

use codec::{Codec, Decode, Encode};
use futures::{future, FutureExt, StreamExt};
use hex::ToHex;
use log::{debug, error, info, trace, warn};
use parking_lot::Mutex;

use sc_client_api::{Backend, FinalityNotification, FinalityNotifications};
use sc_network_gossip::GossipEngine;

use sp_api::BlockId;
use sp_application_crypto::{AppPublic, Public};
use sp_arithmetic::traits::AtLeast32Bit;
use sp_core::Pair;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block, Header, NumberFor},
	SaturatedConversion,
};

use beefy_primitives::{
	BeefyApi, Commitment, ConsensusLog, MmrRootHash, SignedCommitment, ValidatorSet, VersionedCommitment, VoteMessage,
	BEEFY_ENGINE_ID, GENESIS_AUTHORITY_SET_ID, KEY_TYPE,
};

use crate::{
	error::{self},
	gossip::{topic, BeefyGossipValidator},
	metric_inc, metric_set,
	metrics::Metrics,
	notification, round, Client,
};

pub(crate) struct WorkerParams<B, P, BE, C>
where
	B: Block,
	P: sp_core::Pair,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
{
	pub client: Arc<C>,
	pub backend: Arc<BE>,
	pub key_store: Option<SyncCryptoStorePtr>,
	pub signed_commitment_sender: notification::BeefySignedCommitmentSender<B, P::Signature>,
	pub gossip_engine: GossipEngine<B>,
	pub gossip_validator: Arc<BeefyGossipValidator<B, P>>,
	pub min_block_delta: u32,
	pub metrics: Option<Metrics>,
}

/// A BEEFY worker plays the BEEFY protocol
pub(crate) struct BeefyWorker<B, C, BE, P>
where
	B: Block,
	BE: Backend<B>,
	P: Pair,
	P::Public: AppPublic + Codec,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	C: Client<B, BE, P>,
{
	client: Arc<C>,
	backend: Arc<BE>,
	key_store: Option<SyncCryptoStorePtr>,
	signed_commitment_sender: notification::BeefySignedCommitmentSender<B, P::Signature>,
	gossip_engine: Arc<Mutex<GossipEngine<B>>>,
	gossip_validator: Arc<BeefyGossipValidator<B, P>>,
	/// Min delta in block numbers between two blocks, BEEFY should vote on
	min_block_delta: u32,
	metrics: Option<Metrics>,
	rounds: round::Rounds<MmrRootHash, NumberFor<B>, P::Public, P::Signature>,
	finality_notifications: FinalityNotifications<B>,
	/// Best block we received a GRANDPA notification for
	best_grandpa_block: NumberFor<B>,
	/// Best block a BEEFY voting round has been concluded for
	best_beefy_block: Option<NumberFor<B>>,
	/// Validator set id for the last signed commitment
	last_signed_id: u64,
	// keep rustc happy
	_backend: PhantomData<BE>,
	_pair: PhantomData<P>,
}

impl<B, C, BE, P> BeefyWorker<B, C, BE, P>
where
	B: Block,
	BE: Backend<B>,
	P: Pair,
	P::Public: AppPublic,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	C: Client<B, BE, P>,
	C::Api: BeefyApi<B, P::Public>,
{
	/// Return a new BEEFY worker instance.
	///
	/// Note that a BEEFY worker is only fully functional if a corresponding
	/// BEEFY pallet has been deployed on-chain.
	///
	/// The BEEFY pallet is needed in order to keep track of the BEEFY authority set.
	pub(crate) fn new(worker_params: WorkerParams<B, P, BE, C>) -> Self {
		let WorkerParams {
			client,
			backend,
			key_store,
			signed_commitment_sender,
			gossip_engine,
			gossip_validator,
			min_block_delta,
			metrics,
		} = worker_params;

		BeefyWorker {
			client: client.clone(),
			backend,
			key_store,
			signed_commitment_sender,
			gossip_engine: Arc::new(Mutex::new(gossip_engine)),
			gossip_validator,
			min_block_delta,
			metrics,
			rounds: round::Rounds::new(ValidatorSet::empty()),
			finality_notifications: client.finality_notification_stream(),
			best_grandpa_block: client.info().finalized_number,
			best_beefy_block: None,
			last_signed_id: 0,
			_backend: PhantomData,
			_pair: PhantomData,
		}
	}
}

impl<B, C, BE, P> BeefyWorker<B, C, BE, P>
where
	B: Block,
	BE: Backend<B>,
	P: Pair,
	P::Public: AppPublic,
	P::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	C: Client<B, BE, P>,
	C::Api: BeefyApi<B, P::Public>,
{
	/// Return `true`, if we should vote on block `number`
	fn should_vote_on(&self, number: NumberFor<B>) -> bool {
		let best_beefy_block = if let Some(block) = self.best_beefy_block {
			block
		} else {
			debug!(target: "beefy", "🥩 Missing best BEEFY block - won't vote for: {:?}", number);
			return false;
		};

		let target = vote_target(self.best_grandpa_block, best_beefy_block, self.min_block_delta);

		trace!(target: "beefy", "🥩 should_vote_on: #{:?}, next_block_to_vote_on: #{:?}", number, target);

		metric_set!(self, beefy_should_vote_on, target);

		number == target
	}

	fn sign_commitment(&self, id: &P::Public, commitment: &[u8]) -> Result<P::Signature, error::Crypto<P::Public>> {
		let key_store = self
			.key_store
			.clone()
			.ok_or_else(|| error::Crypto::CannotSign((*id).clone(), "Missing KeyStore".into()))?;

		let sig = SyncCryptoStore::sign_with(&*key_store, KEY_TYPE, &id.to_public_crypto_pair(), commitment)
			.map_err(|e| error::Crypto::CannotSign((*id).clone(), e.to_string()))?
			.ok_or_else(|| error::Crypto::CannotSign((*id).clone(), "No key in KeyStore found".into()))?;

		let sig = sig
			.clone()
			.try_into()
			.map_err(|_| error::Crypto::InvalidSignature(sig.encode_hex(), (*id).clone()))?;

		Ok(sig)
	}

	/// Return the current active validator set at header `header`.
	///
	/// Note that the validator set could be `None`. This is the case if we don't find
	/// a BEEFY authority set change and we can't fetch the authority set from the
	/// BEEFY on-chain state.
	///
	/// Such a failure is usually an indication that the BEEFT pallet has not been deployed (yet).
	fn validator_set(&self, header: &B::Header) -> Option<ValidatorSet<P::Public>> {
		if let Some(new) = find_authorities_change::<B, P::Public>(header) {
			Some(new)
		} else {
			let at = BlockId::hash(header.hash());
			self.client.runtime_api().validator_set(&at).ok()
		}
	}

	/// Return the local authority id.
	///
	/// `None` is returned, if we are not permitted to vote
	fn local_id(&self) -> Option<P::Public> {
		let key_store = self.key_store.clone()?;

		self.rounds
			.validators()
			.iter()
			.find(|id| SyncCryptoStore::has_keys(&*key_store, &[(id.to_raw_vec(), KEY_TYPE)]))
			.cloned()
	}

	fn handle_finality_notification(&mut self, notification: FinalityNotification<B>) {
		trace!(target: "beefy", "🥩 Finality notification: {:?}", notification);

		// update best GRANDPA finalized block we have seen
		self.best_grandpa_block = *notification.header.number();

		if let Some(active) = self.validator_set(&notification.header) {
			// Authority set change or genesis set id triggers new voting rounds
			//
			// TODO: (adoerr) Enacting a new authority set will also implicitly 'conclude'
			// the currently active BEEFY voting round by starting a new one. This is
			// temporary and needs to be replaced by proper round life cycle handling.
			if active.id != self.rounds.validator_set_id()
				|| (active.id == GENESIS_AUTHORITY_SET_ID && self.best_beefy_block.is_none())
			{
				debug!(target: "beefy", "🥩 New active validator set id: {:?}", active);
				metric_set!(self, beefy_validator_set_id, active.id);

				// BEEFY should produce a signed commitment for each session
				if active.id != self.last_signed_id + 1 && active.id != GENESIS_AUTHORITY_SET_ID {
					metric_inc!(self, beefy_skipped_sessions);
				}

				self.rounds = round::Rounds::new(active.clone());

				debug!(target: "beefy", "🥩 New Rounds for id: {:?}", active.id);

				self.best_beefy_block = Some(*notification.header.number());

				// this metric is kind of 'fake'. Best BEEFY block should only be updated once we have a
				// signed commitment for the block. Remove once the above TODO is done.
				metric_set!(self, beefy_best_block, *notification.header.number());
			}
		}

		if self.should_vote_on(*notification.header.number()) {
			let local_id = if let Some(id) = self.local_id() {
				id
			} else {
				trace!(target: "beefy", "🥩 Missing validator id - can't vote for: {:?}", notification.header.hash());
				return;
			};

			let mmr_root = if let Some(hash) = find_mmr_root_digest::<B, P::Public>(&notification.header) {
				hash
			} else {
				warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}", notification.header.hash());
				return;
			};

			let commitment = Commitment {
				payload: mmr_root,
				block_number: notification.header.number(),
				validator_set_id: self.rounds.validator_set_id(),
			};

			let signature = match self.sign_commitment(&local_id, commitment.encode().as_ref()) {
				Ok(sig) => sig,
				Err(err) => {
					warn!(target: "beefy", "🥩 Error signing commitment: {:?}", err);
					return;
				}
			};

			let message = VoteMessage {
				commitment,
				id: local_id,
				signature,
			};

			let encoded_message = message.encode();

			metric_inc!(self, beefy_votes_sent);

			debug!(target: "beefy", "🥩 Sent vote message: {:?}", message);

			self.handle_vote(
				(message.commitment.payload, *message.commitment.block_number),
				(message.id, message.signature),
			);

			self.gossip_engine
				.lock()
				.gossip_message(topic::<B>(), encoded_message, false);
		}
	}

	fn handle_vote(&mut self, round: (MmrRootHash, NumberFor<B>), vote: (P::Public, P::Signature)) {
		self.gossip_validator.note_round(round.1);

		let vote_added = self.rounds.add_vote(round, vote);

		if vote_added && self.rounds.is_done(&round) {
			if let Some(signatures) = self.rounds.drop(&round) {
				// id is stored for skipped session metric calculation
				self.last_signed_id = self.rounds.validator_set_id();

				let commitment = Commitment {
					payload: round.0,
					block_number: round.1,
					validator_set_id: self.last_signed_id,
				};

				let signed_commitment = SignedCommitment { commitment, signatures };

				metric_set!(self, beefy_round_concluded, round.1);

				info!(target: "beefy", "🥩 Round #{} concluded, committed: {:?}.", round.1, signed_commitment);

				if self
					.backend
					.append_justification(
						BlockId::Number(round.1),
						(
							BEEFY_ENGINE_ID,
							VersionedCommitment::V1(signed_commitment.clone()).encode(),
						),
					)
					.is_err()
				{
					// this is a warning for now, because until the round lifecycle is improved, we will
					// conclude certain rounds multiple times.
					warn!(target: "beefy", "🥩 Failed to append justification: {:?}", signed_commitment);
				}

				self.signed_commitment_sender.notify(signed_commitment);
				self.best_beefy_block = Some(round.1);

				metric_set!(self, beefy_best_block, round.1);
			}
		}
	}

	pub(crate) async fn run(mut self) {
		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<B>()).filter_map(
			|notification| async move {
				trace!(target: "beefy", "🥩 Got vote message: {:?}", notification);

				VoteMessage::<MmrRootHash, NumberFor<B>, P::Public, P::Signature>::decode(
					&mut &notification.message[..],
				)
				.ok()
			},
		));

		loop {
			let engine = self.gossip_engine.clone();
			let gossip_engine = future::poll_fn(|cx| engine.lock().poll_unpin(cx));

			futures::select! {
				notification = self.finality_notifications.next().fuse() => {
					if let Some(notification) = notification {
						self.handle_finality_notification(notification);
					} else {
						return;
					}
				},
				vote = votes.next().fuse() => {
					if let Some(vote) = vote {
						self.handle_vote(
							(vote.commitment.payload, vote.commitment.block_number),
							(vote.id, vote.signature),
						);
					} else {
						return;
					}
				},
				_ = gossip_engine.fuse() => {
					error!(target: "beefy", "🥩 Gossip engine has terminated.");
					return;
				}
			}
		}
	}
}

/// Extract the MMR root hash from a digest in the given header, if it exists.
fn find_mmr_root_digest<B, Id>(header: &B::Header) -> Option<MmrRootHash>
where
	B: Block,
	Id: Codec,
{
	header.digest().logs().iter().find_map(|log| {
		match log.try_to::<ConsensusLog<Id>>(OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID)) {
			Some(ConsensusLog::MmrRoot(root)) => Some(root),
			_ => None,
		}
	})
}

/// Scan the `header` digest log for a BEEFY validator set change. Return either the new
/// validator set or `None` in case no validator set change has been signaled.
fn find_authorities_change<B, Id>(header: &B::Header) -> Option<ValidatorSet<Id>>
where
	B: Block,
	Id: Codec,
{
	let id = OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID);

	let filter = |log: ConsensusLog<Id>| match log {
		ConsensusLog::AuthoritiesChange(validator_set) => Some(validator_set),
		_ => None,
	};

	header.digest().convert_first(|l| l.try_to(id).and_then(filter))
}

/// Calculate next block number to vote on
fn vote_target<N>(best_grandpa: N, best_beefy: N, min_delta: u32) -> N
where
	N: AtLeast32Bit + Copy + Debug,
{
	let diff = best_grandpa.saturating_sub(best_beefy);
	let diff = diff.saturated_into::<u32>();
	let target = best_beefy + min_delta.max(diff.next_power_of_two()).into();

	trace!(
		target: "beefy",
		"🥩 vote target - diff: {:?}, next_power_of_two: {:?}, target block: #{:?}",
		diff,
		diff.next_power_of_two(),
		target,
	);

	target
}

#[cfg(test)]
mod tests {
	use super::vote_target;

	#[test]
	fn vote_on_min_block_delta() {
		let t = vote_target(1u32, 0, 4);
		assert_eq!(4, t);
		let t = vote_target(2u32, 0, 4);
		assert_eq!(4, t);
		let t = vote_target(3u32, 0, 4);
		assert_eq!(4, t);
		let t = vote_target(4u32, 0, 4);
		assert_eq!(4, t);

		let t = vote_target(4u32, 4, 4);
		assert_eq!(8, t);

		let t = vote_target(10u32, 10, 4);
		assert_eq!(14, t);
		let t = vote_target(11u32, 10, 4);
		assert_eq!(14, t);
		let t = vote_target(12u32, 10, 4);
		assert_eq!(14, t);
		let t = vote_target(13u32, 10, 4);
		assert_eq!(14, t);

		let t = vote_target(10u32, 10, 8);
		assert_eq!(18, t);
		let t = vote_target(11u32, 10, 8);
		assert_eq!(18, t);
		let t = vote_target(12u32, 10, 8);
		assert_eq!(18, t);
		let t = vote_target(13u32, 10, 8);
		assert_eq!(18, t);
	}

	#[test]
	fn vote_on_power_of_two() {
		let t = vote_target(1008u32, 1000, 4);
		assert_eq!(1008, t);

		let t = vote_target(1016u32, 1000, 4);
		assert_eq!(1016, t);

		let t = vote_target(1032u32, 1000, 4);
		assert_eq!(1032, t);

		let t = vote_target(1064u32, 1000, 4);
		assert_eq!(1064, t);

		let t = vote_target(1128u32, 1000, 4);
		assert_eq!(1128, t);

		let t = vote_target(1256u32, 1000, 4);
		assert_eq!(1256, t);

		let t = vote_target(1512u32, 1000, 4);
		assert_eq!(1512, t);

		let t = vote_target(1024u32, 0, 4);
		assert_eq!(1024, t);
	}

	#[test]
	fn vote_on_target_block() {
		let t = vote_target(1008u32, 1002, 4);
		assert_eq!(1010, t);
		let t = vote_target(1010u32, 1002, 4);
		assert_eq!(1010, t);

		let t = vote_target(1016u32, 1006, 4);
		assert_eq!(1022, t);
		let t = vote_target(1022u32, 1006, 4);
		assert_eq!(1022, t);

		let t = vote_target(1032u32, 1012, 4);
		assert_eq!(1044, t);
		let t = vote_target(1044u32, 1012, 4);
		assert_eq!(1044, t);

		let t = vote_target(1064u32, 1014, 4);
		assert_eq!(1078, t);
		let t = vote_target(1078u32, 1014, 4);
		assert_eq!(1078, t);

		let t = vote_target(1128u32, 1008, 4);
		assert_eq!(1136, t);
		let t = vote_target(1136u32, 1008, 4);
		assert_eq!(1136, t);
	}
}
