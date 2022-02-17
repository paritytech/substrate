// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use std::{collections::BTreeSet, fmt::Debug, marker::PhantomData, sync::Arc};

use codec::{Codec, Decode, Encode};
use futures::{channel::mpsc, future, FutureExt, StreamExt};
use log::{debug, error, info, log_enabled, trace, warn};
use parking_lot::Mutex;

use sc_client_api::{Backend, FinalityNotification, FinalityNotifications};
use sc_network_gossip::GossipEngine;

use sp_api::BlockId;
use sp_arithmetic::traits::AtLeast32Bit;
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block, Header, NumberFor},
	SaturatedConversion,
};

use beefy_primitives::{
	crypto::{AuthorityId, Public, Signature},
	known_payload_ids, BeefyApi, Commitment, ConsensusLog, MmrRootHash, Payload, SignedCommitment,
	ValidatorSet, VersionedFinalityProof, VoteMessage, BEEFY_ENGINE_ID, GENESIS_AUTHORITY_SET_ID,
};

use crate::{
	error,
	gossip::{topic, GossipValidator},
	keystore::BeefyKeystore,
	metric_inc, metric_set,
	metrics::Metrics,
	notification::{BeefyBestBlockSender, BeefySignedCommitmentSender},
	round, Client,
};

pub(crate) struct WorkerParams<B, BE, C>
where
	B: Block,
{
	pub client: Arc<C>,
	pub backend: Arc<BE>,
	pub key_store: BeefyKeystore,
	pub signed_commitment_sender: BeefySignedCommitmentSender<B>,
	pub beefy_best_block_sender: BeefyBestBlockSender<B>,
	pub gossip_engine: GossipEngine<B>,
	pub gossip_validator: Arc<GossipValidator<B>>,
	pub min_block_delta: u32,
	pub metrics: Option<Metrics>,
}

/// A BEEFY worker plays the BEEFY protocol
pub(crate) struct BeefyWorker<B, C, BE>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
{
	client: Arc<C>,
	backend: Arc<BE>,
	key_store: BeefyKeystore,
	signed_commitment_sender: BeefySignedCommitmentSender<B>,
	gossip_engine: Arc<Mutex<GossipEngine<B>>>,
	gossip_validator: Arc<GossipValidator<B>>,
	/// Min delta in block numbers between two blocks, BEEFY should vote on
	min_block_delta: u32,
	metrics: Option<Metrics>,
	rounds: Option<round::Rounds<Payload, NumberFor<B>>>,
	finality_notifications: FinalityNotifications<B>,
	/// Best block we received a GRANDPA notification for
	best_grandpa_block_header: <B as Block>::Header,
	/// Best block a BEEFY voting round has been concluded for
	best_beefy_block: Option<NumberFor<B>>,
	/// Used to keep RPC worker up to date on latest/best beefy
	beefy_best_block_sender: BeefyBestBlockSender<B>,
	/// Validator set id for the last signed commitment
	last_signed_id: u64,
	waker_rx: mpsc::Receiver<()>,
	waker_tx: mpsc::Sender<()>,
	// keep rustc happy
	_backend: PhantomData<BE>,
}

impl<B, C, BE> BeefyWorker<B, C, BE>
where
	B: Block + Codec,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
{
	/// Return a new BEEFY worker instance.
	///
	/// Note that a BEEFY worker is only fully functional if a corresponding
	/// BEEFY pallet has been deployed on-chain.
	///
	/// The BEEFY pallet is needed in order to keep track of the BEEFY authority set.
	pub(crate) fn new(worker_params: WorkerParams<B, BE, C>) -> Self {
		let WorkerParams {
			client,
			backend,
			key_store,
			signed_commitment_sender,
			beefy_best_block_sender,
			gossip_engine,
			gossip_validator,
			min_block_delta,
			metrics,
		} = worker_params;

		let last_finalized_header = client
			.header(BlockId::number(client.info().finalized_number))
			// TODO: is this proof correct in all cases?
			.expect("latest block always has header available; qed.")
			.expect("latest block always has header available; qed.");

		let (waker_tx, waker_rx) = mpsc::channel(10);
		BeefyWorker {
			client: client.clone(),
			backend,
			key_store,
			signed_commitment_sender,
			gossip_engine: Arc::new(Mutex::new(gossip_engine)),
			gossip_validator,
			min_block_delta,
			metrics,
			rounds: None,
			finality_notifications: client.finality_notification_stream(),
			best_grandpa_block_header: last_finalized_header,
			best_beefy_block: None,
			last_signed_id: 0,
			beefy_best_block_sender,
			waker_rx,
			waker_tx,
			_backend: PhantomData,
		}
	}
}

impl<B, C, BE> BeefyWorker<B, C, BE>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
{
	/// Return `true`, if we should vote on block `number`
	fn should_vote_on(&self, number: NumberFor<B>) -> bool {
		let best_beefy_block = if let Some(block) = self.best_beefy_block {
			block
		} else {
			debug!(target: "beefy", "🥩 Missing best BEEFY block - won't vote for: {:?}", number);
			return false
		};

		// FIXME: use correct session_start
		let target = vote_target(
			*self.best_grandpa_block_header.number(),
			best_beefy_block,
			best_beefy_block,
			self.min_block_delta,
		);

		trace!(target: "beefy", "🥩 should_vote_on: #{:?}, next_block_to_vote_on: #{:?}", number, target);

		metric_set!(self, beefy_should_vote_on, target);

		number == target
	}

	/// Return the current active validator set at header `header`.
	///
	/// Note that the validator set could be `None`. This is the case if we don't find
	/// a BEEFY authority set change and we can't fetch the authority set from the
	/// BEEFY on-chain state.
	///
	/// Such a failure is usually an indication that the BEEFY pallet has not been deployed (yet).
	fn validator_set(&self, header: &B::Header) -> Option<ValidatorSet<Public>> {
		let new = if let Some(new) = find_authorities_change::<B>(header) {
			Some(new)
		} else {
			let at = BlockId::hash(header.hash());
			self.client.runtime_api().validator_set(&at).ok().flatten()
		};

		trace!(target: "beefy", "🥩 active validator set: {:?}", new);

		new
	}

	/// Verify `active` validator set for `block` against the key store
	///
	/// The critical case is, if we do have a public key in the key store which is not
	/// part of the active validator set.
	///
	/// Note that for a non-authority node there will be no keystore, and we will
	/// return an error and don't check. The error can usually be ignored.
	fn verify_validator_set(
		&self,
		block: &NumberFor<B>,
		active: &ValidatorSet<Public>,
	) -> Result<(), error::Error> {
		let active: BTreeSet<&Public> = active.validators().iter().collect();

		let public_keys = self.key_store.public_keys()?;
		let store: BTreeSet<&Public> = public_keys.iter().collect();

		let missing: Vec<_> = store.difference(&active).cloned().collect();

		if !missing.is_empty() {
			debug!(target: "beefy", "🥩 for block {:?} public key missing in validator set: {:?}", block, missing);
		}

		Ok(())
	}

	fn handle_finality_notification(&mut self, notification: FinalityNotification<B>) {
		trace!(target: "beefy", "🥩 Finality notification: {:?}", notification);

		// update best GRANDPA finalized block we have seen
		self.best_grandpa_block_header = notification.header;

		warn!(target: "beefy", "🥩 new session, waking up ticker");
		let _ = self.waker_tx.try_send(());
	}

	fn handle_vote(&mut self, round: (Payload, NumberFor<B>), vote: (Public, Signature)) {
		self.gossip_validator.note_round(round.1);

		let rounds = if let Some(rounds) = self.rounds.as_mut() {
			rounds
		} else {
			debug!(target: "beefy", "🥩 Missing validator set - can't handle vote {:?}", vote);
			return
		};

		let vote_added = rounds.add_vote(&round, vote);

		if vote_added && rounds.is_done() {
			if let Some(signatures) = rounds.drop(&round) {
				// id is stored for skipped session metric calculation
				self.last_signed_id = rounds.validator_set_id();

				let block_num = round.1;
				let commitment = Commitment {
					payload: round.0,
					block_number: block_num,
					validator_set_id: self.last_signed_id,
				};

				let signed_commitment = SignedCommitment { commitment, signatures };

				metric_set!(self, beefy_round_concluded, block_num);

				info!(target: "beefy", "🥩 Round #{} concluded, committed: {:?}.", round.1, signed_commitment);

				if self
					.backend
					.append_justification(
						BlockId::Number(block_num),
						(
							BEEFY_ENGINE_ID,
							VersionedFinalityProof::V1(signed_commitment.clone()).encode(),
						),
					)
					.is_err()
				{
					// just a trace, because until the round lifecycle is improved, we will
					// conclude certain rounds multiple times.
					trace!(target: "beefy", "🥩 Failed to append justification: {:?}", signed_commitment);
				}
				self.signed_commitment_sender
					.notify(|| Ok::<_, ()>(signed_commitment))
					.expect("forwards closure result; the closure always returns Ok; qed.");

				self.set_best_beefy_block(block_num, None);

				warn!(target: "beefy", "🥩 round concluded, waking up ticker");
				let _ = self.waker_tx.try_send(());
			}
		}
	}

	/// Set best BEEFY block to `block_num`.
	///
	/// Also sends/updates the best BEEFY block hash to the RPC worker.
	/// If the hash is not explicitly provided in `opt_block_hash`,
	/// this function just gets it from the `Client`.
	fn set_best_beefy_block(
		&mut self,
		block_num: NumberFor<B>,
		mut opt_block_hash: Option<<<B as Block>::Header as Header>::Hash>,
	) {
		if opt_block_hash.is_none() {
			// Try to get block hash ourselves.
			opt_block_hash = match self.client.hash(block_num) {
				Ok(h) => h,
				Err(e) => {
					error!(target: "beefy", "🥩 Failed to get hash for block number {}: {}",
						block_num, e);
					None
				},
			}
		};
		// Update RPC worker with new best BEEFY block hash.
		opt_block_hash.map(|hash| {
			self.beefy_best_block_sender
				.notify(|| Ok::<_, ()>(hash))
				.expect("forwards closure result; the closure always returns Ok; qed.")
		});
		// Set new best BEEFY block number.
		self.best_beefy_block = Some(block_num);

		// FIXME: this metric is kind of 'fake'. Best BEEFY block should only be updated once we
		// have a signed commitment for the block.
		metric_set!(self, beefy_best_block, block_num);
	}

	// fn initialize_best_beefy(&mut self) -> NumberFor<B> {
	// 	// FIXME: currently hardcoded to genesis/block #0.
	// 	let best_beefy = NumberFor::<B>::from(0u32);
	// 	self.set_best_beefy_block(best_beefy, None);
	// 	best_beefy
	// }

	/// Return first block number pertaining to same session as `header`.
	fn session_start_for_header(&self, header: &B::Header) -> NumberFor<B> {
		// Current header is also the session start.
		if let Some(_) = find_authorities_change::<B>(header) {
			return *header.number()
		}

		// Walk up the chain looking for the session change digest.
		let mut parent_hash = *header.parent_hash();
		while parent_hash != Default::default() {
			let header = self
				.client
				.expect_header(BlockId::Hash(parent_hash))
				// TODO: is this proof correct?
				.expect("header always available when following parent hash; qed.");
			if let Some(_) = find_authorities_change::<B>(&header) {
				// Found it! This header is the first of the session.
				break
			}
			parent_hash = *header.parent_hash();
		}
		*header.number()
	}

	/// Handle potential session changes by starting new voting round for mandatory blocks.
	///
	/// Return current session start.
	fn handle_session_change(&mut self) -> NumberFor<B> {
		if let Some(active) = self.validator_set(&self.best_grandpa_block_header) {
			// If validator set has changed compared to the one in our active round,
			if self.rounds.is_none() ||
				active.id() != self.rounds.as_ref().unwrap().validator_set_id()
			{
				// Find new session_start and start new round for mandatory block.
				let session_start = self.session_start_for_header(&self.best_grandpa_block_header);

				debug!(target: "beefy", "🥩 New active validator set: {:?}", active);
				metric_set!(self, beefy_validator_set_id, active.id());
				// BEEFY should produce a signed commitment for each session
				if active.id() != GENESIS_AUTHORITY_SET_ID && active.id() != self.last_signed_id + 1
				{
					metric_inc!(self, beefy_skipped_sessions);
				}

				if log_enabled!(target: "beefy", log::Level::Debug) {
					// verify the new validator set - only do it if we're also logging the warning
					let _ =
						self.verify_validator_set(self.best_grandpa_block_header.number(), &active);
				}

				// // FIXME: Temporary here, remove this block
				// let payload = {
				// 	let mmr_root = if let Some(hash) =
				// 		find_mmr_root_digest::<B, Public>(&self.best_grandpa_block_header)
				// 	{
				// 		hash
				// 	} else {
				// 		warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}",
				// self.best_grandpa_block_header.hash()); 		return
				// 	};
				// 	Payload::new(known_payload_ids::MMR_ROOT_ID, mmr_root.encode())
				// };
				// let block_num = *self.best_grandpa_block_header.number();
				// self.rounds = Some(round::Rounds::new(payload, block_num, active));
				//
				// self.set_best_beefy_block(block_num,
				// Some(self.best_grandpa_block_header.hash()));

				let id = active.id();
				self.rounds = Some(round::Rounds::new(session_start, active));
				debug!(target: "beefy", "🥩 New Rounds for validator set id: {:?} with session_start {:?}", id, session_start);

				session_start
			} else {
				// Otherwise, use same session_start.
				*self.rounds.as_ref().unwrap().session_start()
			}
		} else {
			// TODO: BEEFY pallet not available, stop beefy worker
			NumberFor::<B>::from(0u32)
		}
	}

	fn tick(&mut self) {
		warn!(target: "beefy", "🥩 TICK...");

		// TODO: check session changed - if true, find new session boundary (mandatory block)
		let _session_start = self.handle_session_change();

		let _target = vote_target(
			*self.best_grandpa_block_header.number(),
			self.best_beefy_block.unwrap_or(0u32.into()),
			self.best_beefy_block.unwrap_or(0u32.into()),
			self.min_block_delta,
		);

		// TODO: avoid multiple ticks for same block

		if self.should_vote_on(*self.best_grandpa_block_header.number()) {
			let (validators, validator_set_id) = if let Some(rounds) = &self.rounds {
				(rounds.validators(), rounds.validator_set_id())
			} else {
				debug!(target: "beefy", "🥩 Missing validator set - can't vote for: {:?}", self.best_grandpa_block_header.hash());
				return
			};
			let authority_id = if let Some(id) = self.key_store.authority_id(validators) {
				debug!(target: "beefy", "🥩 Local authority id: {:?}", id);
				id
			} else {
				debug!(target: "beefy", "🥩 Missing validator id - can't vote for: {:?}", self.best_grandpa_block_header.hash());
				return
			};

			let mmr_root = if let Some(hash) =
				find_mmr_root_digest::<B, Public>(&self.best_grandpa_block_header)
			{
				hash
			} else {
				warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}", self.best_grandpa_block_header.hash());
				return
			};

			let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, mmr_root.encode());
			let commitment = Commitment {
				payload,
				block_number: *self.best_grandpa_block_header.number(),
				validator_set_id,
			};
			let encoded_commitment = commitment.encode();

			let signature = match self.key_store.sign(&authority_id, &*encoded_commitment) {
				Ok(sig) => sig,
				Err(err) => {
					warn!(target: "beefy", "🥩 Error signing commitment: {:?}", err);
					return
				},
			};

			trace!(
				target: "beefy",
				"🥩 Produced signature using {:?}, is_valid: {:?}",
				authority_id,
				BeefyKeystore::verify(&authority_id, &signature, &*encoded_commitment)
			);

			let message = VoteMessage { commitment, id: authority_id, signature };

			let encoded_message = message.encode();

			metric_inc!(self, beefy_votes_sent);

			debug!(target: "beefy", "🥩 Sent vote message: {:?}", message);

			self.handle_vote(
				(message.commitment.payload, message.commitment.block_number),
				(message.id, message.signature),
			);

			self.gossip_engine.lock().gossip_message(topic::<B>(), encoded_message, false);
		}
	}

	pub(crate) async fn run(mut self) {
		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<B>()).filter_map(
			|notification| async move {
				debug!(target: "beefy", "🥩 Got vote message: {:?}", notification);

				VoteMessage::<NumberFor<B>, Public, Signature>::decode(
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
				_ = self.waker_rx.next().fuse() => {
					self.tick();
				},
				_ = gossip_engine.fuse() => {
					error!(target: "beefy", "🥩 Gossip engine has terminated.");
					return;
				}
			}
		}
	}
}

// impl<B, C, BE> Stream for BeefyWorker<B, C, BE>
// where
// 	B: Block + Codec,
// 	BE: Backend<B>,
// 	C: Client<B, BE>,
// 	C::Api: BeefyApi<B>,
// {
//     type Item = ();
//     fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<()>> {
//         unimplemented!()
//     }
// }

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
fn find_authorities_change<B>(header: &B::Header) -> Option<ValidatorSet<AuthorityId>>
where
	B: Block,
{
	let id = OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID);

	let filter = |log: ConsensusLog<AuthorityId>| match log {
		ConsensusLog::AuthoritiesChange(validator_set) => Some(validator_set),
		_ => None,
	};

	header.digest().convert_first(|l| l.try_to(id).and_then(filter))
}

/// Calculate next block number to vote on
fn vote_target<N>(best_grandpa: N, best_beefy: N, session_start: N, min_delta: u32) -> N
where
	N: AtLeast32Bit + Copy + Debug,
{
	// if the mandatory block (session_start) does not have a beefy justification yet,
	// we vote on it
	if best_beefy < session_start {
		trace!(
			target: "beefy",
			"🥩 vote target - mandatory block: #{:?}",
			session_start,
		);

		session_start
	} else {
		let diff = best_grandpa.saturating_sub(best_beefy) + 1u32.into();
		let diff = diff.saturated_into::<u32>() / 2;
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
