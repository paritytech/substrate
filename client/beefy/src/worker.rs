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
use log::{debug, error, trace, warn};
use parking_lot::Mutex;

use sc_client_api::{Backend, FinalityNotification, FinalityNotifications};
use sc_network_gossip::GossipEngine;

use sp_api::BlockId;
use sp_application_crypto::{AppPublic, Public};
use sp_core::Pair;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block, Header, NumberFor, Zero},
};

use beefy_primitives::{
	BeefyApi, Commitment, ConsensusLog, MmrRootHash, SignedCommitment, ValidatorSet, VoteMessage, BEEFY_ENGINE_ID,
	GENESIS_AUTHORITY_SET_ID, KEY_TYPE,
};

use crate::{
	error::{self},
	metric_inc, metric_set,
	metrics::Metrics,
	notification, round,
	validator::{topic, BeefyGossipValidator},
	Client,
};

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
	key_store: SyncCryptoStorePtr,
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
	/// Best block this node has voted for
	best_block_voted_on: NumberFor<B>,
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
	pub(crate) fn new(
		client: Arc<C>,
		key_store: SyncCryptoStorePtr,
		signed_commitment_sender: notification::BeefySignedCommitmentSender<B, P::Signature>,
		gossip_engine: GossipEngine<B>,
		gossip_validator: Arc<BeefyGossipValidator<B, P>>,
		min_block_delta: u32,
		metrics: Option<Metrics>,
	) -> Self {
		BeefyWorker {
			client: client.clone(),
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
			best_block_voted_on: Zero::zero(),
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
		use sp_runtime::{traits::Saturating, SaturatedConversion};

		let best_beefy_block = if let Some(block) = self.best_beefy_block {
			block
		} else {
			debug!(target: "beefy", "🥩 Missing best BEEFY block - won't vote for: {:?}", number);
			return false;
		};

		let diff = self.best_grandpa_block.saturating_sub(best_beefy_block);
		let diff = diff.saturated_into::<u32>();
		let next_power_of_two = (diff / 2).next_power_of_two();
		let next_block_to_vote_on = self.best_block_voted_on + self.min_block_delta.max(next_power_of_two).into();

		trace!(
			target: "beefy",
			"should_vote_on: #{:?}, diff: {:?}, next_power_of_two: {:?}, next_block_to_vote_on: #{:?}",
			number,
			diff,
			next_power_of_two,
			next_block_to_vote_on,
		);

		metric_set!(self, beefy_should_vote_on, next_block_to_vote_on);

		number == next_block_to_vote_on
	}

	fn sign_commitment(&self, id: &P::Public, commitment: &[u8]) -> Result<P::Signature, error::Crypto<P::Public>> {
		let sig = SyncCryptoStore::sign_with(&*self.key_store, KEY_TYPE, &id.to_public_crypto_pair(), &commitment)
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
		self.rounds
			.validators()
			.iter()
			.find(|id| SyncCryptoStore::has_keys(&*self.key_store, &[(id.to_raw_vec(), KEY_TYPE)]))
			.cloned()
	}

	fn handle_finality_notification(&mut self, notification: FinalityNotification<B>) {
		debug!(target: "beefy", "🥩 Finality notification: {:?}", notification);

		// update best GRANDPA finalized block we have seen
		self.best_grandpa_block = *notification.header.number();

		if let Some(active) = self.validator_set(&notification.header) {
			debug!(target: "beefy", "🥩 Active validator set id: {:?}", active);

			metric_set!(self, beefy_validator_set_id, active.id);

			// BEEFY should produce a signed commitment for each session
			if (active.id != GENESIS_AUTHORITY_SET_ID) && (active.id != (1 + self.last_signed_id)) {
				metric_inc!(self, beefy_skipped_sessions);
			}

			// Authority set change or genesis set id triggers new voting rounds
			//
			// TODO: (adoerr) Enacting a new authority set will also implicitly 'conclude'
			// the currently active BEEFY voting round by starting a new one. This is
			// temporary and needs to be repalced by proper round life cycle handling.
			if (active.id != self.rounds.validator_set_id()) || (active.id == GENESIS_AUTHORITY_SET_ID) {
				self.rounds = round::Rounds::new(active.clone());

				debug!(target: "beefy", "🥩 New Rounds for id: {:?}", active.id);

				self.best_beefy_block = Some(*notification.header.number());

				// this metric is kind of 'fake'. Best BEEFY block should only be updated once we have a
				// signed commitment for the block. Remove once the above TODO is done.
				metric_set!(self, beefy_best_block, *notification.header.number());
			}
		};

		if self.should_vote_on(*notification.header.number()) {
			let local_id = if let Some(id) = self.local_id() {
				id
			} else {
				debug!(target: "beefy", "🥩 Missing validator id - can't vote for: {:?}", notification.header.hash());
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

			self.best_block_voted_on = *notification.header.number();

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

				debug!(target: "beefy", "🥩 Round #{} concluded, committed: {:?}.", round.1, signed_commitment);

				self.signed_commitment_sender.notify(signed_commitment);
				self.best_beefy_block = Some(round.1);

				metric_set!(self, beefy_best_block, round.1);
			}
		}
	}

	pub(crate) async fn run(mut self) {
		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<B>()).filter_map(
			|notification| async move {
				debug!(target: "beefy", "🥩 Got vote message: {:?}", notification);

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
