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

use std::{collections::BTreeSet, fmt::Debug, marker::PhantomData, sync::Arc, time::Duration};

use codec::{Codec, Decode, Encode};
use futures::{future, FutureExt, StreamExt};
use log::{debug, error, info, log_enabled, trace, warn};
use parking_lot::Mutex;

use sc_client_api::{Backend, FinalityNotification, FinalityNotifications};
use sc_network_gossip::GossipEngine;

use sp_api::BlockId;
use sp_arithmetic::traits::AtLeast32Bit;
use sp_consensus::SyncOracle;
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block, Header, NumberFor},
	SaturatedConversion,
};

use beefy_primitives::{
	crypto::{AuthorityId, Signature},
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
	round::Rounds,
	Client,
};

pub(crate) struct WorkerParams<B, BE, C, SO>
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
	pub sync_oracle: SO,
}

/// A BEEFY worker plays the BEEFY protocol
pub(crate) struct BeefyWorker<B, C, BE, SO>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	SO: SyncOracle + Send + Sync + Clone + 'static,
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
	rounds: Option<Rounds<Payload, B>>,
	finality_notifications: FinalityNotifications<B>,
	/// Best block we received a GRANDPA notification for
	best_grandpa_block_header: <B as Block>::Header,
	/// Best block a BEEFY voting round has been concluded for
	best_beefy_block: Option<NumberFor<B>>,
	/// Used to keep RPC worker up to date on latest/best beefy
	beefy_best_block_sender: BeefyBestBlockSender<B>,
	/// Validator set id for the last signed commitment
	last_signed_id: u64,
	/// Handle to the sync oracle
	sync_oracle: SO,
	// keep rustc happy
	_backend: PhantomData<BE>,
	#[cfg(test)]
	// behavior modifiers used in tests
	test_res: tests::TestModifiers,
}

impl<B, C, BE, SO> BeefyWorker<B, C, BE, SO>
where
	B: Block + Codec,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
	SO: SyncOracle + Send + Sync + Clone + 'static,
{
	/// Return a new BEEFY worker instance.
	///
	/// Note that a BEEFY worker is only fully functional if a corresponding
	/// BEEFY pallet has been deployed on-chain.
	///
	/// The BEEFY pallet is needed in order to keep track of the BEEFY authority set.
	pub(crate) fn new(
		worker_params: WorkerParams<B, BE, C, SO>,
		#[cfg(test)]
		// behavior modifiers used in tests
		test_res: tests::TestModifiers,
	) -> Self {
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
			sync_oracle,
		} = worker_params;

		let last_finalized_header = client
			.expect_header(BlockId::number(client.info().finalized_number))
			.expect("latest block always has header available; qed.");

		BeefyWorker {
			client: client.clone(),
			backend,
			key_store,
			signed_commitment_sender,
			gossip_engine: Arc::new(Mutex::new(gossip_engine)),
			gossip_validator,
			// always target at least one block better than current best beefy
			min_block_delta: min_block_delta.max(1),
			metrics,
			rounds: None,
			finality_notifications: client.finality_notification_stream(),
			best_grandpa_block_header: last_finalized_header,
			best_beefy_block: None,
			last_signed_id: 0,
			beefy_best_block_sender,
			sync_oracle,
			_backend: PhantomData,
			#[cfg(test)]
			test_res,
		}
	}
}

impl<B, C, BE, SO> BeefyWorker<B, C, BE, SO>
where
	B: Block,
	BE: Backend<B>,
	C: Client<B, BE>,
	C::Api: BeefyApi<B>,
	SO: SyncOracle + Send + Sync + Clone + 'static,
{
	/// Return `Some(number)` if we should be voting on block `number` now,
	/// return `None` if there is no block we should vote on now.
	fn current_vote_target(&self) -> Option<NumberFor<B>> {
		let rounds = if let Some(r) = &self.rounds {
			r
		} else {
			debug!(target: "beefy", "🥩 No voting round started");
			return None
		};

		let best_finalized = *self.best_grandpa_block_header.number();
		// `target` is guaranteed > `best_beefy` since `min_block_delta` is at least `1`.
		let target = vote_target(
			best_finalized,
			self.best_beefy_block,
			*rounds.session_start(),
			self.min_block_delta,
		);
		trace!(
			target: "beefy",
			"🥩 best beefy: #{:?}, best finalized: #{:?}, current_vote_target: {:?}",
			self.best_beefy_block,
			best_finalized,
			target
		);
		if let Some(target) = &target {
			metric_set!(self, beefy_should_vote_on, target);
		}
		target
	}

	/// Verify `active` validator set for `block` against the key store
	///
	/// We want to make sure that we have _at least one_ key in our keystore that
	/// is part of the validator set, that's because if there are no local keys
	/// then we can't perform our job as a validator.
	///
	/// Note that for a non-authority node there will be no keystore, and we will
	/// return an error and don't check. The error can usually be ignored.
	fn verify_validator_set(
		&self,
		block: &NumberFor<B>,
		active: &ValidatorSet<AuthorityId>,
	) -> Result<(), error::Error> {
		let active: BTreeSet<&AuthorityId> = active.validators().iter().collect();

		let public_keys = self.key_store.public_keys()?;
		let store: BTreeSet<&AuthorityId> = public_keys.iter().collect();

		if store.intersection(&active).count() == 0 {
			let msg = "no authority public key found in store".to_string();
			debug!(target: "beefy", "🥩 for block {:?} {}", block, msg);
			Err(error::Error::Keystore(msg))
		} else {
			Ok(())
		}
	}

	/// Set best BEEFY block to `block_num`.
	///
	/// Also sends/updates the best BEEFY block hash to the RPC worker.
	fn set_best_beefy_block(&mut self, block_num: NumberFor<B>) {
		if Some(block_num) > self.best_beefy_block {
			// Try to get block hash ourselves.
			let block_hash = match self.client.hash(block_num) {
				Ok(h) => h,
				Err(e) => {
					error!(target: "beefy", "🥩 Failed to get hash for block number {}: {}",
						block_num, e);
					None
				},
			};
			// Update RPC worker with new best BEEFY block hash.
			block_hash.map(|hash| {
				self.beefy_best_block_sender
					.notify(|| Ok::<_, ()>(hash))
					.expect("forwards closure result; the closure always returns Ok; qed.")
			});
			// Set new best BEEFY block number.
			self.best_beefy_block = Some(block_num);
			metric_set!(self, beefy_best_block, block_num);
		} else {
			debug!(target: "beefy", "🥩 Can't set best beefy to older: {}", block_num);
		}
	}

	/// Handle session changes by starting new voting round for mandatory blocks.
	fn init_session_at(&mut self, active: ValidatorSet<AuthorityId>, session_start: NumberFor<B>) {
		debug!(target: "beefy", "🥩 New active validator set: {:?}", active);
		metric_set!(self, beefy_validator_set_id, active.id());
		// BEEFY should produce a signed commitment for each session
		if active.id() != self.last_signed_id + 1 && active.id() != GENESIS_AUTHORITY_SET_ID {
			metric_inc!(self, beefy_skipped_sessions);
		}

		if log_enabled!(target: "beefy", log::Level::Debug) {
			// verify the new validator set - only do it if we're also logging the warning
			let _ = self.verify_validator_set(&session_start, &active);
		}

		let prev_validator_set = if let Some(r) = &self.rounds {
			r.validator_set().clone()
		} else {
			// no previous rounds present use new validator set instead (genesis case)
			active.clone()
		};
		let id = active.id();
		self.rounds = Some(Rounds::new(session_start, active, prev_validator_set));
		info!(target: "beefy", "🥩 New Rounds for validator set id: {:?} with session_start {:?}", id, session_start);
	}

	fn handle_finality_notification(&mut self, notification: &FinalityNotification<B>) {
		trace!(target: "beefy", "🥩 Finality notification: {:?}", notification);
		let number = *notification.header.number();

		// On start-up ignore old finality notifications that we're not interested in.
		if number <= *self.best_grandpa_block_header.number() {
			debug!(target: "beefy", "🥩 Got unexpected finality for old block #{:?}", number);
			return
		}

		// update best GRANDPA finalized block we have seen
		self.best_grandpa_block_header = notification.header.clone();

		self.handle_finality(&notification.header);
	}

	fn handle_finality(&mut self, header: &B::Header) {
		// Check for and handle potential new session.
		if let Some(new_validator_set) = find_authorities_change::<B>(header) {
			self.init_session_at(new_validator_set, *header.number());
		}

		// Vote if there's now a new vote target.
		if let Some(target_number) = self.current_vote_target() {
			self.do_vote(target_number);
		}
	}

	fn handle_vote(
		&mut self,
		round: (Payload, NumberFor<B>),
		vote: (AuthorityId, Signature),
		self_vote: bool,
	) {
		self.gossip_validator.note_round(round.1);

		let rounds = if let Some(rounds) = self.rounds.as_mut() {
			rounds
		} else {
			debug!(target: "beefy", "🥩 Missing validator set - can't handle vote {:?}", vote);
			return
		};

		if rounds.add_vote(&round, vote, self_vote) {
			if let Some(signatures) = rounds.try_conclude(&round) {
				self.gossip_validator.conclude_round(round.1);

				// id is stored for skipped session metric calculation
				self.last_signed_id = rounds.validator_set_id_for(round.1);

				let block_num = round.1;
				let commitment = Commitment {
					payload: round.0,
					block_number: block_num,
					validator_set_id: self.last_signed_id,
				};

				let signed_commitment = SignedCommitment { commitment, signatures };

				metric_set!(self, beefy_round_concluded, block_num);

				info!(target: "beefy", "🥩 Round #{} concluded, committed: {:?}.", round.1, signed_commitment);

				if let Err(e) = self.backend.append_justification(
					BlockId::Number(block_num),
					(
						BEEFY_ENGINE_ID,
						VersionedFinalityProof::V1(signed_commitment.clone()).encode(),
					),
				) {
					trace!(target: "beefy", "🥩 Error {:?} on appending justification: {:?}", e, signed_commitment);
				}
				self.signed_commitment_sender
					.notify(|| Ok::<_, ()>(signed_commitment))
					.expect("forwards closure result; the closure always returns Ok; qed.");

				self.set_best_beefy_block(block_num);

				// Vote if there's now a new vote target.
				if let Some(target_number) = self.current_vote_target() {
					self.do_vote(target_number);
				}
			}
		}
	}

	/// Create and gossip Signed Commitment for block number `target_number`.
	///
	/// Also handle this self vote by calling `self.handle_vote()` for it.
	fn do_vote(&mut self, target_number: NumberFor<B>) {
		trace!(target: "beefy", "🥩 Try voting on {}", target_number);

		// Most of the time we get here, `target` is actually `best_grandpa`,
		// avoid asking `client` for header in that case.
		let target_header = if target_number == *self.best_grandpa_block_header.number() {
			self.best_grandpa_block_header.clone()
		} else {
			match self.client.expect_header(BlockId::Number(target_number)) {
				Ok(h) => h,
				Err(err) => {
					debug!(
						target: "beefy",
						"🥩 Could not get header for block #{:?} (error: {:?}), skipping vote..",
						target_number,
						err
					);
					return
				},
			}
		};
		let target_hash = target_header.hash();

		let mmr_root = if let Some(hash) = self.extract_mmr_root_digest(&target_header) {
			hash
		} else {
			warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}", target_hash);
			return
		};
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, mmr_root.encode());

		let (validators, validator_set_id) = if let Some(rounds) = &self.rounds {
			if !rounds.should_self_vote(&(payload.clone(), target_number)) {
				debug!(target: "beefy", "🥩 Don't double vote for block number: {:?}", target_number);
				return
			}
			(rounds.validators_for(target_number), rounds.validator_set_id_for(target_number))
		} else {
			debug!(target: "beefy", "🥩 Missing validator set - can't vote for: {:?}", target_hash);
			return
		};
		let authority_id = if let Some(id) = self.key_store.authority_id(validators) {
			debug!(target: "beefy", "🥩 Local authority id: {:?}", id);
			id
		} else {
			debug!(target: "beefy", "🥩 Missing validator id - can't vote for: {:?}", target_hash);
			return
		};

		let commitment = Commitment { payload, block_number: target_number, validator_set_id };
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
			true,
		);

		self.gossip_engine.lock().gossip_message(topic::<B>(), encoded_message, false);
	}

	/// Wait for BEEFY runtime pallet to be available.
	#[cfg(not(test))]
	async fn wait_for_runtime_pallet(&mut self) {
		self.client
			.finality_notification_stream()
			.take_while(|notif| {
				let at = BlockId::hash(notif.header.hash());
				if let Some(active) = self.client.runtime_api().validator_set(&at).ok().flatten() {
					if active.id() == GENESIS_AUTHORITY_SET_ID {
						// When starting from genesis, there is no session boundary digest.
						// Just initialize `rounds` to Block #1 as BEEFY mandatory block.
						self.init_session_at(active, 1u32.into());
					}
					// In all other cases, we just go without `rounds` initialized, meaning the
					// worker won't vote until it witnesses a session change.
					// Once we'll implement 'initial sync' (catch-up), the worker will be able to
					// start voting right away.
					self.handle_finality_notification(notif);
					future::ready(false)
				} else {
					trace!(target: "beefy", "🥩 Finality notification: {:?}", notif);
					trace!(target: "beefy", "🥩 Waiting for BEEFY pallet to become available...");
					future::ready(true)
				}
			})
			.for_each(|_| future::ready(()))
			.await;
		// get a new stream that provides _new_ notifications (from here on out)
		self.finality_notifications = self.client.finality_notification_stream();
	}

	/// For tests don't use runtime pallet. Start rounds from block #1.
	#[cfg(test)]
	async fn wait_for_runtime_pallet(&mut self) {
		let active = self.test_res.active_validators.clone();
		self.init_session_at(active, 1u32.into());
	}

	/// Main loop for BEEFY worker.
	///
	/// Wait for BEEFY runtime pallet to be available, then start the main async loop
	/// which is driven by finality notifications and gossiped votes.
	pub(crate) async fn run(mut self) {
		info!(target: "beefy", "🥩 run BEEFY worker, best grandpa: #{:?}.", self.best_grandpa_block_header.number());
		self.wait_for_runtime_pallet().await;

		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<B>()).filter_map(
			|notification| async move {
				debug!(target: "beefy", "🥩 Got vote message: {:?}", notification);

				VoteMessage::<NumberFor<B>, AuthorityId, Signature>::decode(
					&mut &notification.message[..],
				)
				.ok()
			},
		));

		loop {
			while self.sync_oracle.is_major_syncing() {
				debug!(target: "beefy", "Waiting for major sync to complete...");
				futures_timer::Delay::new(Duration::from_secs(5)).await;
			}

			let engine = self.gossip_engine.clone();
			let gossip_engine = future::poll_fn(|cx| engine.lock().poll_unpin(cx));

			futures::select! {
				notification = self.finality_notifications.next().fuse() => {
					if let Some(notification) = notification {
						self.handle_finality_notification(&notification);
					} else {
						return;
					}
				},
				vote = votes.next().fuse() => {
					if let Some(vote) = vote {
						self.handle_vote(
							(vote.commitment.payload, vote.commitment.block_number),
							(vote.id, vote.signature),
							false
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

	/// Simple wrapper over mmr root extraction.
	#[cfg(not(test))]
	fn extract_mmr_root_digest(&self, header: &B::Header) -> Option<MmrRootHash> {
		find_mmr_root_digest::<B>(header)
	}

	/// For tests, have the option to modify mmr root.
	#[cfg(test)]
	fn extract_mmr_root_digest(&self, header: &B::Header) -> Option<MmrRootHash> {
		let mut mmr_root = find_mmr_root_digest::<B>(header);
		if self.test_res.corrupt_mmr_roots {
			mmr_root.as_mut().map(|hash| *hash ^= MmrRootHash::random());
		}
		mmr_root
	}
}

/// Extract the MMR root hash from a digest in the given header, if it exists.
fn find_mmr_root_digest<B>(header: &B::Header) -> Option<MmrRootHash>
where
	B: Block,
{
	let id = OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID);

	let filter = |log: ConsensusLog<AuthorityId>| match log {
		ConsensusLog::MmrRoot(root) => Some(root),
		_ => None,
	};
	header.digest().convert_first(|l| l.try_to(id).and_then(filter))
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

/// Calculate next block number to vote on.
///
/// Return `None` if there is no voteable target yet.
fn vote_target<N>(
	best_grandpa: N,
	best_beefy: Option<N>,
	session_start: N,
	min_delta: u32,
) -> Option<N>
where
	N: AtLeast32Bit + Copy + Debug,
{
	// if the mandatory block (session_start) does not have a beefy justification yet,
	// we vote on it
	let target = match best_beefy {
		None => {
			trace!(
				target: "beefy",
				"🥩 vote target - mandatory block: #{:?}",
				session_start,
			);
			session_start
		},
		Some(bbb) if bbb < session_start => {
			trace!(
				target: "beefy",
				"🥩 vote target - mandatory block: #{:?}",
				session_start,
			);
			session_start
		},
		Some(bbb) => {
			let diff = best_grandpa.saturating_sub(bbb) + 1u32.into();
			let diff = diff.saturated_into::<u32>() / 2;
			let target = bbb + min_delta.max(diff.next_power_of_two()).into();

			trace!(
				target: "beefy",
				"🥩 vote target - diff: {:?}, next_power_of_two: {:?}, target block: #{:?}",
				diff,
				diff.next_power_of_two(),
				target,
			);

			target
		},
	};

	// Don't vote for targets until they've been finalized
	// (`target` can be > `best_grandpa` when `min_delta` is big enough).
	if target > best_grandpa {
		None
	} else {
		Some(target)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::{
		keystore::tests::Keyring,
		tests::{create_beefy_worker, get_beefy_streams, make_beefy_ids, BeefyTestNet},
	};

	use futures::{executor::block_on, future::poll_fn, task::Poll};

	use sc_client_api::HeaderBackend;
	use sc_network::NetworkService;
	use sc_network_test::{PeersFullClient, TestNetFactory};
	use sp_api::HeaderT;
	use substrate_test_runtime_client::{
		runtime::{Block, Digest, DigestItem, Header, H256},
		Backend,
	};

	#[derive(Clone)]
	pub struct TestModifiers {
		pub active_validators: ValidatorSet<AuthorityId>,
		pub corrupt_mmr_roots: bool,
	}

	#[test]
	fn vote_on_min_block_delta() {
		let t = vote_target(1u32, Some(1), 1, 4);
		assert_eq!(None, t);
		let t = vote_target(2u32, Some(1), 1, 4);
		assert_eq!(None, t);
		let t = vote_target(4u32, Some(2), 1, 4);
		assert_eq!(None, t);
		let t = vote_target(6u32, Some(2), 1, 4);
		assert_eq!(Some(6), t);

		let t = vote_target(9u32, Some(4), 1, 4);
		assert_eq!(Some(8), t);

		let t = vote_target(10u32, Some(10), 1, 8);
		assert_eq!(None, t);
		let t = vote_target(12u32, Some(10), 1, 8);
		assert_eq!(None, t);
		let t = vote_target(18u32, Some(10), 1, 8);
		assert_eq!(Some(18), t);
	}

	#[test]
	fn vote_on_power_of_two() {
		let t = vote_target(1008u32, Some(1000), 1, 4);
		assert_eq!(Some(1004), t);

		let t = vote_target(1016u32, Some(1000), 1, 4);
		assert_eq!(Some(1008), t);

		let t = vote_target(1032u32, Some(1000), 1, 4);
		assert_eq!(Some(1016), t);

		let t = vote_target(1064u32, Some(1000), 1, 4);
		assert_eq!(Some(1032), t);

		let t = vote_target(1128u32, Some(1000), 1, 4);
		assert_eq!(Some(1064), t);

		let t = vote_target(1256u32, Some(1000), 1, 4);
		assert_eq!(Some(1128), t);

		let t = vote_target(1512u32, Some(1000), 1, 4);
		assert_eq!(Some(1256), t);

		let t = vote_target(1024u32, Some(1), 1, 4);
		assert_eq!(Some(513), t);
	}

	#[test]
	fn vote_on_target_block() {
		let t = vote_target(1008u32, Some(1002), 1, 4);
		assert_eq!(Some(1006), t);
		let t = vote_target(1010u32, Some(1002), 1, 4);
		assert_eq!(Some(1006), t);

		let t = vote_target(1016u32, Some(1006), 1, 4);
		assert_eq!(Some(1014), t);
		let t = vote_target(1022u32, Some(1006), 1, 4);
		assert_eq!(Some(1014), t);

		let t = vote_target(1032u32, Some(1012), 1, 4);
		assert_eq!(Some(1028), t);
		let t = vote_target(1044u32, Some(1012), 1, 4);
		assert_eq!(Some(1028), t);

		let t = vote_target(1064u32, Some(1014), 1, 4);
		assert_eq!(Some(1046), t);
		let t = vote_target(1078u32, Some(1014), 1, 4);
		assert_eq!(Some(1046), t);

		let t = vote_target(1128u32, Some(1008), 1, 4);
		assert_eq!(Some(1072), t);
		let t = vote_target(1136u32, Some(1008), 1, 4);
		assert_eq!(Some(1072), t);
	}

	#[test]
	fn vote_on_mandatory_block() {
		let t = vote_target(1008u32, Some(1002), 1004, 4);
		assert_eq!(Some(1004), t);
		let t = vote_target(1016u32, Some(1006), 1007, 4);
		assert_eq!(Some(1007), t);
		let t = vote_target(1064u32, Some(1014), 1063, 4);
		assert_eq!(Some(1063), t);
		let t = vote_target(1320u32, Some(1012), 1234, 4);
		assert_eq!(Some(1234), t);

		let t = vote_target(1128u32, Some(1008), 1008, 4);
		assert_eq!(Some(1072), t);
	}

	#[test]
	fn extract_authorities_change_digest() {
		let mut header = Header::new(
			1u32.into(),
			Default::default(),
			Default::default(),
			Default::default(),
			Digest::default(),
		);

		// verify empty digest shows nothing
		assert!(find_authorities_change::<Block>(&header).is_none());

		let peers = &[Keyring::One, Keyring::Two];
		let id = 42;
		let validator_set = ValidatorSet::new(make_beefy_ids(peers), id).unwrap();
		header.digest_mut().push(DigestItem::Consensus(
			BEEFY_ENGINE_ID,
			ConsensusLog::<AuthorityId>::AuthoritiesChange(validator_set.clone()).encode(),
		));

		// verify validator set is correctly extracted from digest
		let extracted = find_authorities_change::<Block>(&header);
		assert_eq!(extracted, Some(validator_set));
	}

	#[test]
	fn extract_mmr_root_digest() {
		let mut header = Header::new(
			1u32.into(),
			Default::default(),
			Default::default(),
			Default::default(),
			Digest::default(),
		);

		// verify empty digest shows nothing
		assert!(find_mmr_root_digest::<Block>(&header).is_none());

		let mmr_root_hash = H256::random();
		header.digest_mut().push(DigestItem::Consensus(
			BEEFY_ENGINE_ID,
			ConsensusLog::<AuthorityId>::MmrRoot(mmr_root_hash.clone()).encode(),
		));

		// verify validator set is correctly extracted from digest
		let extracted = find_mmr_root_digest::<Block>(&header);
		assert_eq!(extracted, Some(mmr_root_hash));
	}

	#[test]
	fn should_vote_target() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1, 0);
		net.peer(0).data.use_validator_set(&validator_set);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);

		// rounds not initialized -> should vote: `None`
		assert_eq!(worker.current_vote_target(), None);

		let set_up = |worker: &mut BeefyWorker<
			Block,
			PeersFullClient,
			Backend,
			Arc<NetworkService<Block, H256>>,
		>,
		              best_grandpa: u64,
		              best_beefy: Option<u64>,
		              session_start: u64,
		              min_delta: u32| {
			let grandpa_header = Header::new(
				best_grandpa,
				Default::default(),
				Default::default(),
				Default::default(),
				Default::default(),
			);
			worker.best_grandpa_block_header = grandpa_header;
			worker.best_beefy_block = best_beefy;
			worker.min_block_delta = min_delta;
			worker.rounds =
				Some(Rounds::new(session_start, validator_set.clone(), validator_set.clone()));
		};

		// under min delta
		set_up(&mut worker, 1, Some(1), 1, 4);
		assert_eq!(worker.current_vote_target(), None);
		set_up(&mut worker, 5, Some(2), 1, 4);
		assert_eq!(worker.current_vote_target(), None);

		// vote on min delta
		set_up(&mut worker, 9, Some(4), 1, 4);
		assert_eq!(worker.current_vote_target(), Some(8));
		set_up(&mut worker, 18, Some(10), 1, 8);
		assert_eq!(worker.current_vote_target(), Some(18));

		// vote on power of two
		set_up(&mut worker, 1008, Some(1000), 1, 1);
		assert_eq!(worker.current_vote_target(), Some(1004));
		set_up(&mut worker, 1016, Some(1000), 1, 2);
		assert_eq!(worker.current_vote_target(), Some(1008));

		// nothing new to vote on
		set_up(&mut worker, 1000, Some(1000), 1, 1);
		assert_eq!(worker.current_vote_target(), None);

		// vote on mandatory
		set_up(&mut worker, 1008, None, 1000, 8);
		assert_eq!(worker.current_vote_target(), Some(1000));
		set_up(&mut worker, 1008, Some(1000), 1001, 8);
		assert_eq!(worker.current_vote_target(), Some(1001));
	}

	#[test]
	fn keystore_vs_validator_set() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1, 0);
		net.peer(0).data.use_validator_set(&validator_set);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);

		// keystore doesn't contain other keys than validators'
		assert_eq!(worker.verify_validator_set(&1, &validator_set), Ok(()));

		// unknown `Bob` key
		let keys = &[Keyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let err_msg = "no authority public key found in store".to_string();
		let expected = Err(error::Error::Keystore(err_msg));
		assert_eq!(worker.verify_validator_set(&1, &validator_set), expected);

		// worker has no keystore
		worker.key_store = None.into();
		let expected_err = Err(error::Error::Keystore("no Keystore".into()));
		assert_eq!(worker.verify_validator_set(&1, &validator_set), expected_err);
	}

	#[test]
	fn setting_best_beefy_block() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1, 0);
		net.peer(0).data.use_validator_set(&validator_set);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);

		let (mut best_block_streams, _) = get_beefy_streams(&mut net, keys);
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();

		// no 'best beefy block'
		assert_eq!(worker.best_beefy_block, None);
		block_on(poll_fn(move |cx| {
			assert_eq!(best_block_stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		}));

		// unknown hash for block #1
		let (mut best_block_streams, _) = get_beefy_streams(&mut net, keys);
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();
		worker.set_best_beefy_block(1);
		assert_eq!(worker.best_beefy_block, Some(1));
		block_on(poll_fn(move |cx| {
			assert_eq!(best_block_stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		}));

		// generate 2 blocks, try again expect success
		let (mut best_block_streams, _) = get_beefy_streams(&mut net, keys);
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();
		net.generate_blocks(2, 10, &validator_set);

		worker.set_best_beefy_block(2);
		assert_eq!(worker.best_beefy_block, Some(2));
		block_on(poll_fn(move |cx| {
			match best_block_stream.poll_next_unpin(cx) {
				// expect Some(hash-of-block-2)
				Poll::Ready(Some(hash)) => {
					let block_num = net.peer(0).client().as_client().number(hash).unwrap();
					assert_eq!(block_num, Some(2));
				},
				v => panic!("unexpected value: {:?}", v),
			}
			Poll::Ready(())
		}));
	}

	#[test]
	fn setting_initial_session() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1, 0);
		net.peer(0).data.use_validator_set(&validator_set);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1);

		assert!(worker.rounds.is_none());

		// verify setting the correct validator sets and boundary for genesis session
		worker.init_session_at(validator_set.clone(), 1);

		let worker_rounds = worker.rounds.as_ref().unwrap();
		assert_eq!(worker_rounds.validator_set(), &validator_set);
		assert_eq!(worker_rounds.session_start(), &1);
		// in genesis case both current and prev validator sets are the same
		assert_eq!(worker_rounds.validator_set_id_for(1), validator_set.id());
		assert_eq!(worker_rounds.validator_set_id_for(2), validator_set.id());

		// new validator set
		let keys = &[Keyring::Bob];
		let new_validator_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();

		// verify setting the correct validator sets and boundary for non-genesis session
		worker.init_session_at(new_validator_set.clone(), 11);

		let worker_rounds = worker.rounds.as_ref().unwrap();
		assert_eq!(worker_rounds.validator_set(), &new_validator_set);
		assert_eq!(worker_rounds.session_start(), &11);
		// mandatory block gets prev set, further blocks get new set
		assert_eq!(worker_rounds.validator_set_id_for(11), validator_set.id());
		assert_eq!(worker_rounds.validator_set_id_for(12), new_validator_set.id());
		assert_eq!(worker_rounds.validator_set_id_for(13), new_validator_set.id());
	}
}
