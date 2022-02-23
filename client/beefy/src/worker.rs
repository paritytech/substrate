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

use std::{collections::BTreeSet, fmt::Debug, marker::PhantomData, pin::Pin, sync::Arc};

use codec::{Codec, Decode, Encode};
use futures::{
	future,
	task::{Context, Poll, Waker},
	FutureExt, Stream, StreamExt,
};
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

#[derive(Default)]
struct BeefyTicker {
	inner: Arc<Mutex<(bool, Option<Waker>)>>,
}

impl BeefyTicker {
	pub fn wake(&mut self) {
		let mut guard = self.inner.lock();
		guard.0 = true;
		guard.1.take().map(|waker| waker.wake());
	}
}

impl Stream for BeefyTicker {
	type Item = ();
	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<()>> {
		let mut guard = self.inner.lock();
		if guard.0 {
			// Just tick every time we're woken up.
			guard.0 = false;
			Poll::Ready(Some(()))
		} else {
			guard.1 = Some(cx.waker().clone());
			Poll::Pending
		}
	}
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
	// Used to wake the main task from the other event stream tasks.
	ticker: BeefyTicker,
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
			ticker: BeefyTicker::default(),
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
		if let Some(target) = &target {
			metric_set!(self, beefy_should_vote_on, target);
		}
		target
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

		trace!(target: "beefy", "🥩 new finalized block, waking up ticker");
		self.ticker.wake();
	}

	fn handle_vote(
		&mut self,
		round: (Payload, NumberFor<B>),
		vote: (Public, Signature),
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
				self.gossip_validator.drop_round(round.1);

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

				trace!(target: "beefy", "🥩 round concluded, waking up ticker");
				self.ticker.wake();
			}
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

	/// Return first block number pertaining to same session as `header`.
	fn session_start_for_header(&self, header: &B::Header) -> NumberFor<B> {
		// Current header is also the session start.
		if let Some(_) = find_authorities_change::<B>(header) {
			return *header.number()
		}

		// Walk up the chain looking for the session change digest.
		let mut header = header.clone();
		let mut parent_hash = *header.parent_hash();
		while parent_hash != Default::default() {
			header = self
				.client
				.expect_header(BlockId::Hash(parent_hash))
				// TODO: is this proof correct?
				.expect("header always available when following parent hash; qed.");
			if let Some(_) = find_authorities_change::<B>(&header) {
				// Found the first header of the session.
				info!(target: "beefy", "🥩 session boundary is: {:?}.", *header.number());
				return *header.number()
			}
			parent_hash = *header.parent_hash();
		}

		info!(target: "beefy", "🥩 no session boundary found, defaulting to block number 1.");
		1u32.into()
	}

	/// Handle potential session changes by starting new voting round for mandatory blocks.
	fn handle_session_change(&mut self) {
		let header = &self.best_grandpa_block_header;
		if let Some(active) = self.validator_set(header) {
			// If validator set has changed compared to the one in our active round,
			if self.rounds.is_none() ||
				active.id() != self.rounds.as_ref().unwrap().validator_set_id()
			{
				// Find new session_start and start new round for mandatory block.
				let session_start = self.session_start_for_header(header);

				debug!(target: "beefy", "🥩 New active validator set: {:?}", active);
				info!(target: "beefy", "🥩 New BEEFY session starting at: {:?}", session_start);
				metric_set!(self, beefy_validator_set_id, active.id());
				// BEEFY should produce a signed commitment for each session
				if active.id() != GENESIS_AUTHORITY_SET_ID && active.id() != self.last_signed_id + 1
				{
					metric_inc!(self, beefy_skipped_sessions);
				}

				if log_enabled!(target: "beefy", log::Level::Debug) {
					// verify the new validator set - only do it if we're also logging the warning
					let _ = self.verify_validator_set(header.number(), &active);
				}

				let id = active.id();
				self.rounds = Some(round::Rounds::new(session_start, active));
				debug!(target: "beefy", "🥩 New Rounds for validator set id: {:?} with session_start {:?}", id, session_start);
			}
		} else {
			// TODO: BEEFY pallet not available, stop beefy worker
			()
		}
	}

	// TODO: doc comment
	// TODO: propagate errors for stopping beefy worker
	fn tick(&mut self) {
		warn!(target: "beefy", "🥩 TICK...");

		// Check for and handle potential new session.
		self.handle_session_change();

		if let Some(target_number) = self.current_vote_target() {
			// Do vote.

			// Most of the time we get here, `target` is actually `best_grandpa`,
			// avoid asking `client` for header in that case.
			let target_header = if target_number == *self.best_grandpa_block_header.number() {
				self.best_grandpa_block_header.clone()
			} else {
				self.client
					.expect_header(BlockId::Number(target_number))
					.expect("FIXME: return error here")
			};
			let target_hash = target_header.hash();

			let mmr_root = if let Some(hash) = find_mmr_root_digest::<B, Public>(&target_header) {
				hash
			} else {
				warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}", target_hash);
				return
			};
			let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, mmr_root.encode());

			if let Some(rounds) = &self.rounds {
				if !rounds.should_vote(&(payload.clone(), target_number)) {
					debug!(target: "beefy", "🥩 Don't double vote for block number: {:?}", target_number);
					return
				}
			};

			let (validators, validator_set_id) = if let Some(rounds) = &self.rounds {
				(rounds.validators(), rounds.validator_set_id())
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
							false
						);
					} else {
						return;
					}
				},
				_ = self.ticker.next().fuse() => {
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
	trace!(target: "beefy", "🥩 best finalized: #{:?}, next_block_to_vote_on: #{:?}", best_grandpa, target);

	// Don't vote for targets until they've been finalized
	// (`target` can be > `best_grandpa` when `min_delta` is big enough).
	if target > best_grandpa {
		None
	} else {
		Some(target)
	}
}

#[cfg(test)]
mod tests {
	use super::vote_target;

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
}
