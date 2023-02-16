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

use crate::{
	communication::{
		gossip::{topic, GossipValidator},
		request_response::outgoing_requests_engine::OnDemandJustificationsEngine,
	},
	error::Error,
	justification::BeefyVersionedFinalityProof,
	keystore::BeefyKeystore,
	metric_get, metric_inc, metric_set,
	metrics::VoterMetrics,
	round::{Rounds, VoteImportResult},
	BeefyVoterLinks, LOG_TARGET,
};
use beefy_primitives::{
	crypto::{AuthorityId, Signature},
	Commitment, ConsensusLog, PayloadProvider, ValidatorSet, VersionedFinalityProof, VoteMessage,
	BEEFY_ENGINE_ID,
};
use codec::{Codec, Decode, Encode};
use futures::{stream::Fuse, FutureExt, StreamExt};
use log::{debug, error, info, log_enabled, trace, warn};
use sc_client_api::{Backend, FinalityNotification, FinalityNotifications, HeaderBackend};
use sc_network_common::service::{NetworkEventStream, NetworkRequest};
use sc_network_gossip::GossipEngine;
use sc_utils::notification::NotificationReceiver;
use sp_api::BlockId;
use sp_arithmetic::traits::{AtLeast32Bit, Saturating};
use sp_consensus::SyncOracle;
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block, ConstU32, Header, NumberFor, Zero},
	BoundedVec, SaturatedConversion,
};
use std::{
	collections::{BTreeMap, BTreeSet, VecDeque},
	fmt::Debug,
	marker::PhantomData,
	sync::Arc,
};

/// Bound for the number of buffered future voting rounds.
const MAX_BUFFERED_VOTE_ROUNDS: usize = 600;
/// Bound for the number of buffered votes per round number.
const MAX_BUFFERED_VOTES_PER_ROUND: u32 = 1000;
/// Bound for the number of pending justifications - use 2400 - the max number
/// of justifications possible in a single session.
const MAX_BUFFERED_JUSTIFICATIONS: usize = 2400;

pub(crate) enum RoundAction {
	Drop,
	Process,
	Enqueue,
}

/// Responsible for the voting strategy.
/// It chooses which incoming votes to accept and which votes to generate.
/// Keeps track of voting seen for current and future rounds.
#[derive(Debug, Decode, Encode, PartialEq)]
pub(crate) struct VoterOracle<B: Block> {
	/// Queue of known sessions. Keeps track of voting rounds (block numbers) within each session.
	///
	/// There are three voter states coresponding to three queue states:
	/// 1. voter uninitialized: queue empty,
	/// 2. up-to-date - all mandatory blocks leading up to current GRANDPA finalized:
	///    queue has ONE element, the 'current session' where `mandatory_done == true`,
	/// 3. lagging behind GRANDPA: queue has [1, N] elements, where all `mandatory_done == false`.
	///    In this state, everytime a session gets its mandatory block BEEFY finalized, it's
	///    popped off the queue, eventually getting to state `2. up-to-date`.
	sessions: VecDeque<Rounds<B>>,
	/// Min delta in block numbers between two blocks, BEEFY should vote on.
	min_block_delta: u32,
}

impl<B: Block> VoterOracle<B> {
	/// Verify provided `sessions` satisfies requirements, then build `VoterOracle`.
	pub fn checked_new(sessions: VecDeque<Rounds<B>>, min_block_delta: u32) -> Option<Self> {
		let mut prev_start = Zero::zero();
		let mut prev_validator_id = None;
		// verifies the
		let mut validate = || -> bool {
			if sessions.is_empty() {
				return false
			}
			for (idx, session) in sessions.iter().enumerate() {
				if session.validators().is_empty() {
					return false
				}
				if session.session_start() <= prev_start {
					return false
				}
				#[cfg(not(test))]
				if let Some(prev_id) = prev_validator_id {
					if session.validator_set_id() <= prev_id {
						return false
					}
				}
				if idx != 0 && session.mandatory_done() {
					return false
				}
				prev_start = session.session_start();
				prev_validator_id = Some(session.validator_set_id());
			}
			true
		};
		if validate() {
			Some(VoterOracle {
				sessions,
				// Always target at least one block better than current best beefy.
				min_block_delta: min_block_delta.max(1),
			})
		} else {
			error!(target: LOG_TARGET, "🥩 Invalid sessions queue: {:?}.", sessions);
			None
		}
	}

	// Return reference to rounds pertaining to first session in the queue.
	// Voting will always happen at the head of the queue.
	fn active_rounds(&self) -> Option<&Rounds<B>> {
		self.sessions.front()
	}

	// Return mutable reference to rounds pertaining to first session in the queue.
	// Voting will always happen at the head of the queue.
	fn active_rounds_mut(&mut self) -> Option<&mut Rounds<B>> {
		self.sessions.front_mut()
	}

	// Prune the sessions queue to keep the Oracle in one of the expected three states.
	//
	// To be called on each BEEFY finality and on each new rounds/session addition.
	fn try_prune(&mut self) {
		if self.sessions.len() > 1 {
			// when there's multiple sessions, only keep the `!mandatory_done()` ones.
			self.sessions.retain(|s| !s.mandatory_done())
		}
	}

	/// Add new observed session to the Oracle.
	pub fn add_session(&mut self, rounds: Rounds<B>) {
		self.sessions.push_back(rounds);
		// Once we add a new session we can drop/prune previous session if it's been finalized.
		self.try_prune();
	}

	/// Finalize a particular block.
	pub fn finalize(&mut self, block: NumberFor<B>) -> Result<(), Error> {
		// Conclude voting round for this block.
		self.active_rounds_mut().ok_or(Error::UninitSession)?.conclude(block);
		// Prune any now "finalized" sessions from queue.
		self.try_prune();
		Ok(())
	}

	/// Return current pending mandatory block, if any, plus its active validator set.
	pub fn mandatory_pending(&self) -> Option<(NumberFor<B>, ValidatorSet<AuthorityId>)> {
		self.sessions.front().and_then(|round| {
			if round.mandatory_done() {
				None
			} else {
				Some((round.session_start(), round.validator_set().clone()))
			}
		})
	}

	/// Return `(A, B)` tuple representing inclusive [A, B] interval of votes to accept.
	pub fn accepted_interval(
		&self,
		best_grandpa: NumberFor<B>,
	) -> Result<(NumberFor<B>, NumberFor<B>), Error> {
		let rounds = self.sessions.front().ok_or(Error::UninitSession)?;

		if rounds.mandatory_done() {
			// There's only one session active and its mandatory is done.
			// Accept any GRANDPA finalized vote.
			Ok((rounds.session_start(), best_grandpa.into()))
		} else {
			// There's at least one session with mandatory not done.
			// Only accept votes for the mandatory block in the front of queue.
			Ok((rounds.session_start(), rounds.session_start()))
		}
	}

	/// Utility function to quickly decide what to do for each round.
	pub fn triage_round(
		&self,
		round: NumberFor<B>,
		best_grandpa: NumberFor<B>,
	) -> Result<RoundAction, Error> {
		let (start, end) = self.accepted_interval(best_grandpa)?;
		if start <= round && round <= end {
			Ok(RoundAction::Process)
		} else if round > end {
			Ok(RoundAction::Enqueue)
		} else {
			Ok(RoundAction::Drop)
		}
	}

	/// Return `Some(number)` if we should be voting on block `number`,
	/// return `None` if there is no block we should vote on.
	pub fn voting_target(
		&self,
		best_beefy: NumberFor<B>,
		best_grandpa: NumberFor<B>,
	) -> Option<NumberFor<B>> {
		let rounds = if let Some(r) = self.sessions.front() {
			r
		} else {
			debug!(target: LOG_TARGET, "🥩 No voting round started");
			return None
		};

		// `target` is guaranteed > `best_beefy` since `min_block_delta` is at least `1`.
		let target =
			vote_target(best_grandpa, best_beefy, rounds.session_start(), self.min_block_delta);
		trace!(
			target: LOG_TARGET,
			"🥩 best beefy: #{:?}, best finalized: #{:?}, current_vote_target: {:?}",
			best_beefy,
			best_grandpa,
			target
		);
		target
	}
}

pub(crate) struct WorkerParams<B: Block, BE, P, N> {
	pub backend: Arc<BE>,
	pub payload_provider: P,
	pub network: N,
	pub key_store: BeefyKeystore,
	pub gossip_engine: GossipEngine<B>,
	pub gossip_validator: Arc<GossipValidator<B>>,
	pub on_demand_justifications: OnDemandJustificationsEngine<B>,
	pub links: BeefyVoterLinks<B>,
	pub metrics: Option<VoterMetrics>,
	pub persisted_state: PersistedState<B>,
}

#[derive(Debug, Decode, Encode, PartialEq)]
pub(crate) struct PersistedState<B: Block> {
	/// Best block we received a GRANDPA finality for.
	best_grandpa_block_header: <B as Block>::Header,
	/// Best block a BEEFY voting round has been concluded for.
	best_beefy_block: NumberFor<B>,
	/// Best block we voted on.
	best_voted: NumberFor<B>,
	/// Chooses which incoming votes to accept and which votes to generate.
	/// Keeps track of voting seen for current and future rounds.
	voting_oracle: VoterOracle<B>,
}

impl<B: Block> PersistedState<B> {
	pub fn checked_new(
		grandpa_header: <B as Block>::Header,
		best_beefy: NumberFor<B>,
		sessions: VecDeque<Rounds<B>>,
		min_block_delta: u32,
	) -> Option<Self> {
		VoterOracle::checked_new(sessions, min_block_delta).map(|voting_oracle| PersistedState {
			best_grandpa_block_header: grandpa_header,
			best_beefy_block: best_beefy,
			best_voted: Zero::zero(),
			voting_oracle,
		})
	}

	pub(crate) fn set_min_block_delta(&mut self, min_block_delta: u32) {
		self.voting_oracle.min_block_delta = min_block_delta.max(1);
	}

	pub(crate) fn set_best_grandpa(&mut self, best_grandpa: <B as Block>::Header) {
		self.best_grandpa_block_header = best_grandpa;
	}
}

/// A BEEFY worker plays the BEEFY protocol
pub(crate) struct BeefyWorker<B: Block, BE, P, N> {
	// utilities
	backend: Arc<BE>,
	payload_provider: P,
	network: N,
	key_store: BeefyKeystore,

	// communication
	gossip_engine: GossipEngine<B>,
	gossip_validator: Arc<GossipValidator<B>>,
	on_demand_justifications: OnDemandJustificationsEngine<B>,

	// channels
	/// Links between the block importer, the background voter and the RPC layer.
	links: BeefyVoterLinks<B>,

	// voter state
	/// BEEFY client metrics.
	metrics: Option<VoterMetrics>,
	/// Buffer holding votes for future processing.
	pending_votes: BTreeMap<
		NumberFor<B>,
		BoundedVec<
			VoteMessage<NumberFor<B>, AuthorityId, Signature>,
			ConstU32<MAX_BUFFERED_VOTES_PER_ROUND>,
		>,
	>,
	/// Buffer holding justifications for future processing.
	pending_justifications: BTreeMap<NumberFor<B>, BeefyVersionedFinalityProof<B>>,
	/// Persisted voter state.
	persisted_state: PersistedState<B>,
}

impl<B, BE, P, N> BeefyWorker<B, BE, P, N>
where
	B: Block + Codec,
	BE: Backend<B>,
	P: PayloadProvider<B>,
	N: NetworkEventStream + NetworkRequest + SyncOracle + Send + Sync + Clone + 'static,
{
	/// Return a new BEEFY worker instance.
	///
	/// Note that a BEEFY worker is only fully functional if a corresponding
	/// BEEFY pallet has been deployed on-chain.
	///
	/// The BEEFY pallet is needed in order to keep track of the BEEFY authority set.
	pub(crate) fn new(worker_params: WorkerParams<B, BE, P, N>) -> Self {
		let WorkerParams {
			backend,
			payload_provider,
			key_store,
			network,
			gossip_engine,
			gossip_validator,
			on_demand_justifications,
			links,
			metrics,
			persisted_state,
		} = worker_params;

		BeefyWorker {
			backend,
			payload_provider,
			network,
			key_store,
			gossip_engine,
			gossip_validator,
			on_demand_justifications,
			links,
			metrics,
			pending_votes: BTreeMap::new(),
			pending_justifications: BTreeMap::new(),
			persisted_state,
		}
	}

	fn best_grandpa_block(&self) -> NumberFor<B> {
		*self.persisted_state.best_grandpa_block_header.number()
	}

	fn best_beefy_block(&self) -> NumberFor<B> {
		self.persisted_state.best_beefy_block
	}

	fn voting_oracle(&self) -> &VoterOracle<B> {
		&self.persisted_state.voting_oracle
	}

	fn active_rounds(&mut self) -> Option<&Rounds<B>> {
		self.persisted_state.voting_oracle.active_rounds()
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
	) -> Result<(), Error> {
		let active: BTreeSet<&AuthorityId> = active.validators().iter().collect();

		let public_keys = self.key_store.public_keys()?;
		let store: BTreeSet<&AuthorityId> = public_keys.iter().collect();

		if store.intersection(&active).count() == 0 {
			let msg = "no authority public key found in store".to_string();
			debug!(target: LOG_TARGET, "🥩 for block {:?} {}", block, msg);
			metric_inc!(self, beefy_no_authority_found_in_store);
			Err(Error::Keystore(msg))
		} else {
			Ok(())
		}
	}

	/// Handle session changes by starting new voting round for mandatory blocks.
	fn init_session_at(
		&mut self,
		validator_set: ValidatorSet<AuthorityId>,
		new_session_start: NumberFor<B>,
	) {
		debug!(target: LOG_TARGET, "🥩 New active validator set: {:?}", validator_set);

		// BEEFY should finalize a mandatory block during each session.
		if let Some(active_session) = self.active_rounds() {
			if !active_session.mandatory_done() {
				debug!(
					target: LOG_TARGET,
					"🥩 New session {} while active session {} is still lagging.",
					validator_set.id(),
					active_session.validator_set_id(),
				);
				metric_inc!(self, beefy_lagging_sessions);
			}
		}

		if log_enabled!(target: LOG_TARGET, log::Level::Debug) {
			// verify the new validator set - only do it if we're also logging the warning
			let _ = self.verify_validator_set(&new_session_start, &validator_set);
		}

		let id = validator_set.id();
		self.persisted_state
			.voting_oracle
			.add_session(Rounds::new(new_session_start, validator_set));
		metric_set!(self, beefy_validator_set_id, id);
		info!(
			target: LOG_TARGET,
			"🥩 New Rounds for validator set id: {:?} with session_start {:?}",
			id,
			new_session_start
		);
	}

	fn handle_finality_notification(&mut self, notification: &FinalityNotification<B>) {
		debug!(target: LOG_TARGET, "🥩 Finality notification: {:?}", notification);
		let header = &notification.header;

		if *header.number() > self.best_grandpa_block() {
			// update best GRANDPA finalized block we have seen
			self.persisted_state.best_grandpa_block_header = header.clone();

			// Check all (newly) finalized blocks for new session(s).
			let backend = self.backend.clone();
			for header in notification
				.tree_route
				.iter()
				.map(|hash| {
					backend
						.blockchain()
						.expect_header(*hash)
						.expect("just finalized block should be available; qed.")
				})
				.chain(std::iter::once(header.clone()))
			{
				if let Some(new_validator_set) = find_authorities_change::<B>(&header) {
					self.init_session_at(new_validator_set, *header.number());
				}
			}
		}
	}

	/// Based on [VoterOracle] this vote is either processed here or enqueued for later.
	fn triage_incoming_vote(
		&mut self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), Error> {
		let block_num = vote.commitment.block_number;
		let best_grandpa = self.best_grandpa_block();
		self.gossip_validator.note_round(block_num);
		match self.voting_oracle().triage_round(block_num, best_grandpa)? {
			RoundAction::Process => self.handle_vote(vote)?,
			RoundAction::Enqueue => {
				debug!(target: LOG_TARGET, "🥩 Buffer vote for round: {:?}.", block_num);
				if self.pending_votes.len() < MAX_BUFFERED_VOTE_ROUNDS {
					let votes_vec = self.pending_votes.entry(block_num).or_default();
					if votes_vec.try_push(vote).is_ok() {
						metric_inc!(self, beefy_buffered_votes);
					} else {
						warn!(
							target: LOG_TARGET,
							"🥩 Buffer vote dropped for round: {:?}", block_num
						);
						metric_inc!(self, beefy_buffered_votes_dropped);
					}
				} else {
					warn!(target: LOG_TARGET, "🥩 Buffer vote dropped for round: {:?}.", block_num);
					metric_inc!(self, beefy_buffered_votes_dropped);
				}
			},
			RoundAction::Drop => metric_inc!(self, beefy_stale_votes),
		};
		Ok(())
	}

	/// Based on [VoterOracle] this justification is either processed here or enqueued for later.
	///
	/// Expects `justification` to be valid.
	fn triage_incoming_justif(
		&mut self,
		justification: BeefyVersionedFinalityProof<B>,
	) -> Result<(), Error> {
		let signed_commitment = match justification {
			VersionedFinalityProof::V1(ref sc) => sc,
		};
		let block_num = signed_commitment.commitment.block_number;
		let best_grandpa = self.best_grandpa_block();
		match self.voting_oracle().triage_round(block_num, best_grandpa)? {
			RoundAction::Process => {
				debug!(target: LOG_TARGET, "🥩 Process justification for round: {:?}.", block_num);
				metric_inc!(self, beefy_imported_justifications);
				self.finalize(justification)?
			},
			RoundAction::Enqueue => {
				debug!(target: LOG_TARGET, "🥩 Buffer justification for round: {:?}.", block_num);
				if self.pending_justifications.len() < MAX_BUFFERED_JUSTIFICATIONS {
					self.pending_justifications.entry(block_num).or_insert(justification);
					metric_inc!(self, beefy_buffered_justifications);
				} else {
					metric_inc!(self, beefy_buffered_justifications_dropped);
					warn!(
						target: LOG_TARGET,
						"🥩 Buffer justification dropped for round: {:?}.", block_num
					);
				}
			},
			RoundAction::Drop => metric_inc!(self, beefy_stale_justifications),
		};
		Ok(())
	}

	fn handle_vote(
		&mut self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), Error> {
		let rounds = self
			.persisted_state
			.voting_oracle
			.active_rounds_mut()
			.ok_or(Error::UninitSession)?;

		let block_number = vote.commitment.block_number;
		match rounds.add_vote(vote) {
			VoteImportResult::RoundConcluded(signed_commitment) => {
				let finality_proof = VersionedFinalityProof::V1(signed_commitment);
				info!(
					target: LOG_TARGET,
					"🥩 Round #{} concluded, finality_proof: {:?}.", block_number, finality_proof
				);
				// We created the `finality_proof` and know to be valid.
				// New state is persisted after finalization.
				self.finalize(finality_proof)?;
			},
			VoteImportResult::Ok => {
				// Persist state after handling mandatory block vote.
				if self
					.voting_oracle()
					.mandatory_pending()
					.map(|(mandatory_num, _)| mandatory_num == block_number)
					.unwrap_or(false)
				{
					crate::aux_schema::write_voter_state(&*self.backend, &self.persisted_state)
						.map_err(|e| Error::Backend(e.to_string()))?;
				}
			},
			VoteImportResult::Equivocation => {
				// TODO: report returned `EquivocationProof` to chain through `pallet-beefy`.
				()
			},
			VoteImportResult::Invalid | VoteImportResult::Stale => (),
		};
		metric_inc!(self, beefy_successful_handled_votes);
		Ok(())
	}

	/// Provide BEEFY finality for block based on `finality_proof`:
	/// 1. Prune now-irrelevant past sessions from the oracle,
	/// 2. Set BEEFY best block,
	/// 3. Persist voter state,
	/// 4. Send best block hash and `finality_proof` to RPC worker.
	///
	/// Expects `finality proof` to be valid.
	fn finalize(&mut self, finality_proof: BeefyVersionedFinalityProof<B>) -> Result<(), Error> {
		let block_num = match finality_proof {
			VersionedFinalityProof::V1(ref sc) => sc.commitment.block_number,
		};

		// Finalize inner round and update voting_oracle state.
		self.persisted_state.voting_oracle.finalize(block_num)?;
		self.gossip_validator.conclude_round(block_num);

		if block_num > self.best_beefy_block() {
			// Set new best BEEFY block number.
			self.persisted_state.best_beefy_block = block_num;
			crate::aux_schema::write_voter_state(&*self.backend, &self.persisted_state)
				.map_err(|e| Error::Backend(e.to_string()))?;

			metric_set!(self, beefy_best_block, block_num);

			self.on_demand_justifications.cancel_requests_older_than(block_num);

			if let Err(e) = self
				.backend
				.blockchain()
				.expect_block_hash_from_id(&BlockId::Number(block_num))
				.and_then(|hash| {
					self.links
						.to_rpc_best_block_sender
						.notify(|| Ok::<_, ()>(hash))
						.expect("forwards closure result; the closure always returns Ok; qed.");

					self.backend
						.append_justification(hash, (BEEFY_ENGINE_ID, finality_proof.encode()))
				}) {
				error!(
					target: LOG_TARGET,
					"🥩 Error {:?} on appending justification: {:?}", e, finality_proof
				);
			}

			self.links
				.to_rpc_justif_sender
				.notify(|| Ok::<_, ()>(finality_proof))
				.expect("forwards closure result; the closure always returns Ok; qed.");
		} else {
			debug!(target: LOG_TARGET, "🥩 Can't set best beefy to old: {}", block_num);
			metric_set!(self, beefy_best_block_set_last_failure, block_num);
		}
		Ok(())
	}

	/// Handle previously buffered justifications and votes that now land in the voting interval.
	fn try_pending_justif_and_votes(&mut self) -> Result<(), Error> {
		let best_grandpa = self.best_grandpa_block();
		let _ph = PhantomData::<B>::default();

		fn to_process_for<B: Block, T>(
			pending: &mut BTreeMap<NumberFor<B>, T>,
			(start, end): (NumberFor<B>, NumberFor<B>),
			_: PhantomData<B>,
		) -> BTreeMap<NumberFor<B>, T> {
			// These are still pending.
			let still_pending = pending.split_off(&end.saturating_add(1u32.into()));
			// These can be processed.
			let to_handle = pending.split_off(&start);
			// The rest can be dropped.
			*pending = still_pending;
			// Return ones to process.
			to_handle
		}
		// Interval of blocks for which we can process justifications and votes right now.
		let mut interval = self.voting_oracle().accepted_interval(best_grandpa)?;

		// Process pending justifications.
		if !self.pending_justifications.is_empty() {
			let justifs_to_handle = to_process_for(&mut self.pending_justifications, interval, _ph);
			for (num, justification) in justifs_to_handle.into_iter() {
				debug!(target: LOG_TARGET, "🥩 Handle buffered justification for: {:?}.", num);
				metric_inc!(self, beefy_imported_justifications);
				if let Err(err) = self.finalize(justification) {
					error!(target: LOG_TARGET, "🥩 Error finalizing block: {}", err);
				}
			}
			metric_set!(self, beefy_buffered_justifications, self.pending_justifications.len());
			// Possibly new interval after processing justifications.
			interval = self.voting_oracle().accepted_interval(best_grandpa)?;
		}

		// Process pending votes.
		if !self.pending_votes.is_empty() {
			let mut processed = 0u64;
			let votes_to_handle = to_process_for(&mut self.pending_votes, interval, _ph);
			for (num, votes) in votes_to_handle.into_iter() {
				debug!(target: LOG_TARGET, "🥩 Handle buffered votes for: {:?}.", num);
				processed += votes.len() as u64;
				for v in votes.into_iter() {
					if let Err(err) = self.handle_vote(v) {
						error!(target: LOG_TARGET, "🥩 Error handling buffered vote: {}", err);
					};
				}
			}
			if let Some(previous) = metric_get!(self, beefy_buffered_votes) {
				previous.sub(processed);
				metric_set!(self, beefy_buffered_votes, previous.get());
			}
		}
		Ok(())
	}

	/// Decide if should vote, then vote.. or don't..
	fn try_to_vote(&mut self) -> Result<(), Error> {
		// Vote if there's now a new vote target.
		if let Some(target) = self
			.voting_oracle()
			.voting_target(self.best_beefy_block(), self.best_grandpa_block())
		{
			metric_set!(self, beefy_should_vote_on, target);
			if target > self.persisted_state.best_voted {
				self.do_vote(target)?;
			}
		}
		Ok(())
	}

	/// Create and gossip Signed Commitment for block number `target_number`.
	///
	/// Also handle this self vote by calling `self.handle_vote()` for it.
	fn do_vote(&mut self, target_number: NumberFor<B>) -> Result<(), Error> {
		debug!(target: LOG_TARGET, "🥩 Try voting on {}", target_number);

		// Most of the time we get here, `target` is actually `best_grandpa`,
		// avoid getting header from backend in that case.
		let target_header = if target_number == self.best_grandpa_block() {
			self.persisted_state.best_grandpa_block_header.clone()
		} else {
			let hash = self
				.backend
				.blockchain()
				.expect_block_hash_from_id(&BlockId::Number(target_number))
				.map_err(|err| {
					let err_msg = format!(
						"Couldn't get hash for block #{:?} (error: {:?}), skipping vote..",
						target_number, err
					);
					Error::Backend(err_msg)
				})?;

			self.backend.blockchain().expect_header(hash).map_err(|err| {
				let err_msg = format!(
					"Couldn't get header for block #{:?} ({:?}) (error: {:?}), skipping vote..",
					target_number, hash, err
				);
				Error::Backend(err_msg)
			})?
		};
		let target_hash = target_header.hash();

		let payload = if let Some(hash) = self.payload_provider.payload(&target_header) {
			hash
		} else {
			warn!(target: LOG_TARGET, "🥩 No MMR root digest found for: {:?}", target_hash);
			return Ok(())
		};

		let rounds = self
			.persisted_state
			.voting_oracle
			.active_rounds_mut()
			.ok_or(Error::UninitSession)?;
		let (validators, validator_set_id) = (rounds.validators(), rounds.validator_set_id());

		let authority_id = if let Some(id) = self.key_store.authority_id(validators) {
			debug!(target: LOG_TARGET, "🥩 Local authority id: {:?}", id);
			id
		} else {
			debug!(
				target: LOG_TARGET,
				"🥩 Missing validator id - can't vote for: {:?}", target_hash
			);
			return Ok(())
		};

		let commitment = Commitment { payload, block_number: target_number, validator_set_id };
		let encoded_commitment = commitment.encode();

		let signature = match self.key_store.sign(&authority_id, &encoded_commitment) {
			Ok(sig) => sig,
			Err(err) => {
				warn!(target: LOG_TARGET, "🥩 Error signing commitment: {:?}", err);
				return Ok(())
			},
		};

		trace!(
			target: LOG_TARGET,
			"🥩 Produced signature using {:?}, is_valid: {:?}",
			authority_id,
			BeefyKeystore::verify(&authority_id, &signature, &encoded_commitment)
		);

		let message = VoteMessage { commitment, id: authority_id, signature };

		let encoded_message = message.encode();

		metric_inc!(self, beefy_votes_sent);

		debug!(target: LOG_TARGET, "🥩 Sent vote message: {:?}", message);

		if let Err(err) = self.handle_vote(message) {
			error!(target: LOG_TARGET, "🥩 Error handling self vote: {}", err);
		}

		self.gossip_engine.gossip_message(topic::<B>(), encoded_message, false);

		// Persist state after vote to avoid double voting in case of voter restarts.
		self.persisted_state.best_voted = target_number;
		metric_set!(self, beefy_best_voted, target_number);
		crate::aux_schema::write_voter_state(&*self.backend, &self.persisted_state)
			.map_err(|e| Error::Backend(e.to_string()))
	}

	fn process_new_state(&mut self) {
		// Handle pending justifications and/or votes for now GRANDPA finalized blocks.
		if let Err(err) = self.try_pending_justif_and_votes() {
			debug!(target: LOG_TARGET, "🥩 {}", err);
		}

		// Don't bother voting or requesting justifications during major sync.
		if !self.network.is_major_syncing() {
			// There were external events, 'state' is changed, author a vote if needed/possible.
			if let Err(err) = self.try_to_vote() {
				debug!(target: LOG_TARGET, "🥩 {}", err);
			}
			// If the current target is a mandatory block,
			// make sure there's also an on-demand justification request out for it.
			if let Some((block, active)) = self.voting_oracle().mandatory_pending() {
				// This only starts new request if there isn't already an active one.
				self.on_demand_justifications.request(block, active);
			}
		}
	}

	/// Main loop for BEEFY worker.
	///
	/// Run the main async loop which is driven by finality notifications and gossiped votes.
	pub(crate) async fn run(
		mut self,
		mut block_import_justif: Fuse<NotificationReceiver<BeefyVersionedFinalityProof<B>>>,
		mut finality_notifications: Fuse<FinalityNotifications<B>>,
	) {
		info!(
			target: LOG_TARGET,
			"🥩 run BEEFY worker, best grandpa: #{:?}.",
			self.best_grandpa_block()
		);

		let mut votes = Box::pin(
			self.gossip_engine
				.messages_for(topic::<B>())
				.filter_map(|notification| async move {
					trace!(target: LOG_TARGET, "🥩 Got vote message: {:?}", notification);

					VoteMessage::<NumberFor<B>, AuthorityId, Signature>::decode(
						&mut &notification.message[..],
					)
					.ok()
				})
				.fuse(),
		);

		loop {
			// Act on changed 'state'.
			self.process_new_state();

			let mut gossip_engine = &mut self.gossip_engine;
			// Wait for, and handle external events.
			// The branches below only change 'state', actual voting happens afterwards,
			// based on the new resulting 'state'.
			futures::select_biased! {
				// Use `select_biased!` to prioritize order below.
				// Make sure to pump gossip engine.
				_ = gossip_engine => {
					error!(target: LOG_TARGET, "🥩 Gossip engine has terminated, closing worker.");
					return;
				},
				// Process finality notifications first since these drive the voter.
				notification = finality_notifications.next() => {
					if let Some(notification) = notification {
						self.handle_finality_notification(&notification);
					} else {
						error!(target: LOG_TARGET, "🥩 Finality stream terminated, closing worker.");
						return;
					}
				},
				// Process incoming justifications as these can make some in-flight votes obsolete.
				justif = self.on_demand_justifications.next().fuse() => {
					if let Some(justif) = justif {
						if let Err(err) = self.triage_incoming_justif(justif) {
							debug!(target: LOG_TARGET, "🥩 {}", err);
						}
					}
				},
				justif = block_import_justif.next() => {
					if let Some(justif) = justif {
						// Block import justifications have already been verified to be valid
						// by `BeefyBlockImport`.
						if let Err(err) = self.triage_incoming_justif(justif) {
							debug!(target: LOG_TARGET, "🥩 {}", err);
						}
					} else {
						error!(target: LOG_TARGET, "🥩 Block import stream terminated, closing worker.");
						return;
					}
				},
				// Finally process incoming votes.
				vote = votes.next() => {
					if let Some(vote) = vote {
						// Votes have already been verified to be valid by the gossip validator.
						if let Err(err) = self.triage_incoming_vote(vote) {
							debug!(target: LOG_TARGET, "🥩 {}", err);
						}
					} else {
						error!(target: LOG_TARGET, "🥩 Votes gossiping stream terminated, closing worker.");
						return;
					}
				},
			}
		}
	}
}

/// Scan the `header` digest log for a BEEFY validator set change. Return either the new
/// validator set or `None` in case no validator set change has been signaled.
pub(crate) fn find_authorities_change<B>(header: &B::Header) -> Option<ValidatorSet<AuthorityId>>
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
fn vote_target<N>(best_grandpa: N, best_beefy: N, session_start: N, min_delta: u32) -> Option<N>
where
	N: AtLeast32Bit + Copy + Debug,
{
	// if the mandatory block (session_start) does not have a beefy justification yet,
	// we vote on it
	let target = if best_beefy < session_start {
		debug!(target: LOG_TARGET, "🥩 vote target - mandatory block: #{:?}", session_start,);
		session_start
	} else {
		let diff = best_grandpa.saturating_sub(best_beefy) + 1u32.into();
		let diff = diff.saturated_into::<u32>() / 2;
		let target = best_beefy + min_delta.max(diff.next_power_of_two()).into();
		trace!(
			target: LOG_TARGET,
			"🥩 vote target - diff: {:?}, next_power_of_two: {:?}, target block: #{:?}",
			diff,
			diff.next_power_of_two(),
			target,
		);

		target
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
		communication::notification::{BeefyBestBlockStream, BeefyVersionedFinalityProofStream},
		tests::{
			create_beefy_keystore, get_beefy_streams, make_beefy_ids, BeefyPeer, BeefyTestNet,
			TestApi,
		},
		BeefyRPCLinks, KnownPeers,
	};
	use beefy_primitives::{
		keyring::Keyring, known_payloads, mmr::MmrRootProvider, Payload, SignedCommitment,
	};
	use futures::{future::poll_fn, task::Poll};
	use parking_lot::Mutex;
	use sc_client_api::{Backend as BackendT, HeaderBackend};
	use sc_network::NetworkService;
	use sc_network_test::TestNetFactory;
	use sp_api::HeaderT;
	use sp_blockchain::Backend as BlockchainBackendT;
	use sp_runtime::traits::One;
	use substrate_test_runtime_client::{
		runtime::{Block, Digest, DigestItem, Header, H256},
		Backend,
	};

	impl<B: super::Block> PersistedState<B> {
		pub fn voting_oracle(&self) -> &VoterOracle<B> {
			&self.voting_oracle
		}

		pub fn active_round(&self) -> Option<&Rounds<B>> {
			self.voting_oracle.active_rounds()
		}

		pub fn best_beefy_block(&self) -> NumberFor<B> {
			self.best_beefy_block
		}

		pub fn best_grandpa_block(&self) -> NumberFor<B> {
			*self.best_grandpa_block_header.number()
		}
	}

	impl<B: super::Block> VoterOracle<B> {
		pub fn sessions(&self) -> &VecDeque<Rounds<B>> {
			&self.sessions
		}
	}

	fn create_beefy_worker(
		peer: &BeefyPeer,
		key: &Keyring,
		min_block_delta: u32,
		genesis_validator_set: ValidatorSet<AuthorityId>,
	) -> BeefyWorker<
		Block,
		Backend,
		MmrRootProvider<Block, TestApi>,
		Arc<NetworkService<Block, H256>>,
	> {
		let keystore = create_beefy_keystore(*key);

		let (to_rpc_justif_sender, from_voter_justif_stream) =
			BeefyVersionedFinalityProofStream::<Block>::channel();
		let (to_rpc_best_block_sender, from_voter_best_beefy_stream) =
			BeefyBestBlockStream::<Block>::channel();
		let (_, from_block_import_justif_stream) =
			BeefyVersionedFinalityProofStream::<Block>::channel();

		let beefy_rpc_links =
			BeefyRPCLinks { from_voter_justif_stream, from_voter_best_beefy_stream };
		*peer.data.beefy_rpc_links.lock() = Some(beefy_rpc_links);

		let links = BeefyVoterLinks {
			from_block_import_justif_stream,
			to_rpc_justif_sender,
			to_rpc_best_block_sender,
		};

		let backend = peer.client().as_backend();
		let api = Arc::new(TestApi::with_validator_set(&genesis_validator_set));
		let network = peer.network_service().clone();
		let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
		let gossip_validator = Arc::new(GossipValidator::new(known_peers.clone()));
		let gossip_engine =
			GossipEngine::new(network.clone(), "/beefy/1", gossip_validator.clone(), None);
		let metrics = None;
		let on_demand_justifications = OnDemandJustificationsEngine::new(
			network.clone(),
			"/beefy/justifs/1".into(),
			known_peers,
			None,
		);
		let genesis_header = backend
			.blockchain()
			.expect_header(backend.blockchain().info().genesis_hash)
			.unwrap();
		let persisted_state = PersistedState::checked_new(
			genesis_header,
			Zero::zero(),
			vec![Rounds::new(One::one(), genesis_validator_set)].into(),
			min_block_delta,
		)
		.unwrap();
		let payload_provider = MmrRootProvider::new(api.clone());
		let worker_params = crate::worker::WorkerParams {
			backend,
			payload_provider,
			key_store: Some(keystore).into(),
			links,
			gossip_engine,
			gossip_validator,
			metrics,
			network,
			on_demand_justifications,
			persisted_state,
		};
		BeefyWorker::<_, _, _, _>::new(worker_params)
	}

	#[test]
	fn vote_on_min_block_delta() {
		let t = vote_target(1u32, 1, 1, 4);
		assert_eq!(None, t);
		let t = vote_target(2u32, 1, 1, 4);
		assert_eq!(None, t);
		let t = vote_target(4u32, 2, 1, 4);
		assert_eq!(None, t);
		let t = vote_target(6u32, 2, 1, 4);
		assert_eq!(Some(6), t);

		let t = vote_target(9u32, 4, 1, 4);
		assert_eq!(Some(8), t);

		let t = vote_target(10u32, 10, 1, 8);
		assert_eq!(None, t);
		let t = vote_target(12u32, 10, 1, 8);
		assert_eq!(None, t);
		let t = vote_target(18u32, 10, 1, 8);
		assert_eq!(Some(18), t);
	}

	#[test]
	fn vote_on_power_of_two() {
		let t = vote_target(1008u32, 1000, 1, 4);
		assert_eq!(Some(1004), t);

		let t = vote_target(1016u32, 1000, 1, 4);
		assert_eq!(Some(1008), t);

		let t = vote_target(1032u32, 1000, 1, 4);
		assert_eq!(Some(1016), t);

		let t = vote_target(1064u32, 1000, 1, 4);
		assert_eq!(Some(1032), t);

		let t = vote_target(1128u32, 1000, 1, 4);
		assert_eq!(Some(1064), t);

		let t = vote_target(1256u32, 1000, 1, 4);
		assert_eq!(Some(1128), t);

		let t = vote_target(1512u32, 1000, 1, 4);
		assert_eq!(Some(1256), t);

		let t = vote_target(1024u32, 1, 1, 4);
		assert_eq!(Some(513), t);
	}

	#[test]
	fn vote_on_target_block() {
		let t = vote_target(1008u32, 1002, 1, 4);
		assert_eq!(Some(1006), t);
		let t = vote_target(1010u32, 1002, 1, 4);
		assert_eq!(Some(1006), t);

		let t = vote_target(1016u32, 1006, 1, 4);
		assert_eq!(Some(1014), t);
		let t = vote_target(1022u32, 1006, 1, 4);
		assert_eq!(Some(1014), t);

		let t = vote_target(1032u32, 1012, 1, 4);
		assert_eq!(Some(1028), t);
		let t = vote_target(1044u32, 1012, 1, 4);
		assert_eq!(Some(1028), t);

		let t = vote_target(1064u32, 1014, 1, 4);
		assert_eq!(Some(1046), t);
		let t = vote_target(1078u32, 1014, 1, 4);
		assert_eq!(Some(1046), t);

		let t = vote_target(1128u32, 1008, 1, 4);
		assert_eq!(Some(1072), t);
		let t = vote_target(1136u32, 1008, 1, 4);
		assert_eq!(Some(1072), t);
	}

	#[test]
	fn vote_on_mandatory_block() {
		let t = vote_target(1008u32, 1002, 1004, 4);
		assert_eq!(Some(1004), t);
		let t = vote_target(1016u32, 1006, 1007, 4);
		assert_eq!(Some(1007), t);
		let t = vote_target(1064u32, 1014, 1063, 4);
		assert_eq!(Some(1063), t);
		let t = vote_target(1320u32, 1012, 1234, 4);
		assert_eq!(Some(1234), t);

		let t = vote_target(1128u32, 1008, 1008, 4);
		assert_eq!(Some(1072), t);
	}

	#[test]
	fn should_vote_target() {
		let mut oracle = VoterOracle::<Block> { min_block_delta: 1, sessions: VecDeque::new() };

		// rounds not initialized -> should vote: `None`
		assert_eq!(oracle.voting_target(0, 1), None);

		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();

		oracle.add_session(Rounds::new(1, validator_set.clone()));

		// under min delta
		oracle.min_block_delta = 4;
		assert_eq!(oracle.voting_target(1, 1), None);
		assert_eq!(oracle.voting_target(2, 5), None);

		// vote on min delta
		assert_eq!(oracle.voting_target(4, 9), Some(8));
		oracle.min_block_delta = 8;
		assert_eq!(oracle.voting_target(10, 18), Some(18));

		// vote on power of two
		oracle.min_block_delta = 1;
		assert_eq!(oracle.voting_target(1000, 1008), Some(1004));
		assert_eq!(oracle.voting_target(1000, 1016), Some(1008));

		// nothing new to vote on
		assert_eq!(oracle.voting_target(1000, 1000), None);

		// vote on mandatory
		oracle.sessions.clear();
		oracle.add_session(Rounds::new(1000, validator_set.clone()));
		assert_eq!(oracle.voting_target(0, 1008), Some(1000));
		oracle.sessions.clear();
		oracle.add_session(Rounds::new(1001, validator_set.clone()));
		assert_eq!(oracle.voting_target(1000, 1008), Some(1001));
	}

	#[test]
	fn test_oracle_accepted_interval() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();

		let mut oracle = VoterOracle::<Block> { min_block_delta: 1, sessions: VecDeque::new() };

		// rounds not initialized -> should accept votes: `None`
		assert!(oracle.accepted_interval(1).is_err());

		let session_one = 1;
		oracle.add_session(Rounds::new(session_one, validator_set.clone()));
		// mandatory not done, only accept mandatory
		for i in 0..15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_one, session_one)));
		}

		// add more sessions, nothing changes
		let session_two = 11;
		let session_three = 21;
		oracle.add_session(Rounds::new(session_two, validator_set.clone()));
		oracle.add_session(Rounds::new(session_three, validator_set.clone()));
		// mandatory not done, should accept mandatory for session_one
		for i in session_three..session_three + 15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_one, session_one)));
		}

		// simulate finish mandatory for session one, prune oracle
		oracle.sessions.front_mut().unwrap().test_set_mandatory_done(true);
		oracle.try_prune();
		// session_one pruned, should accept mandatory for session_two
		for i in session_three..session_three + 15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_two, session_two)));
		}

		// simulate finish mandatory for session two, prune oracle
		oracle.sessions.front_mut().unwrap().test_set_mandatory_done(true);
		oracle.try_prune();
		// session_two pruned, should accept mandatory for session_three
		for i in session_three..session_three + 15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_three, session_three)));
		}

		// simulate finish mandatory for session three
		oracle.sessions.front_mut().unwrap().test_set_mandatory_done(true);
		// verify all other blocks in this session are now open to voting
		for i in session_three..session_three + 15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_three, i)));
		}
		// pruning does nothing in this case
		oracle.try_prune();
		for i in session_three..session_three + 15 {
			assert_eq!(oracle.accepted_interval(i), Ok((session_three, i)));
		}

		// adding new session automatically prunes "finalized" previous session
		let session_four = 31;
		oracle.add_session(Rounds::new(session_four, validator_set.clone()));
		assert_eq!(oracle.sessions.front().unwrap().session_start(), session_four);
		assert_eq!(oracle.accepted_interval(session_four + 10), Ok((session_four, session_four)));
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

	#[tokio::test]
	async fn keystore_vs_validator_set() {
		let keys = &[Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1, validator_set.clone());

		// keystore doesn't contain other keys than validators'
		assert_eq!(worker.verify_validator_set(&1, &validator_set), Ok(()));

		// unknown `Bob` key
		let keys = &[Keyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let err_msg = "no authority public key found in store".to_string();
		let expected = Err(Error::Keystore(err_msg));
		assert_eq!(worker.verify_validator_set(&1, &validator_set), expected);

		// worker has no keystore
		worker.key_store = None.into();
		let expected_err = Err(Error::Keystore("no Keystore".into()));
		assert_eq!(worker.verify_validator_set(&1, &validator_set), expected_err);
	}

	#[tokio::test]
	async fn should_finalize_correctly() {
		let keys = [Keyring::Alice];
		let validator_set = ValidatorSet::new(make_beefy_ids(&keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let backend = net.peer(0).client().as_backend();
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1, validator_set.clone());
		// remove default session, will manually add custom one.
		worker.persisted_state.voting_oracle.sessions.clear();

		let keys = keys.iter().cloned().enumerate();
		let (mut best_block_streams, mut finality_proofs) =
			get_beefy_streams(&mut net, keys.clone());
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();
		let mut finality_proof = finality_proofs.drain(..).next().unwrap();

		let create_finality_proof = |block_num: NumberFor<Block>| {
			let commitment = Commitment {
				payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
				block_number: block_num,
				validator_set_id: validator_set.id(),
			};
			VersionedFinalityProof::V1(SignedCommitment { commitment, signatures: vec![None] })
		};

		// no 'best beefy block' or finality proofs
		assert_eq!(worker.best_beefy_block(), 0);
		poll_fn(move |cx| {
			assert_eq!(best_block_stream.poll_next_unpin(cx), Poll::Pending);
			assert_eq!(finality_proof.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;

		// unknown hash for block #1
		let (mut best_block_streams, mut finality_proofs) =
			get_beefy_streams(&mut net, keys.clone());
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();
		let mut finality_proof = finality_proofs.drain(..).next().unwrap();
		let justif = create_finality_proof(1);
		// create new session at block #1
		worker
			.persisted_state
			.voting_oracle
			.add_session(Rounds::new(1, validator_set.clone()));
		// try to finalize block #1
		worker.finalize(justif.clone()).unwrap();
		// verify block finalized
		assert_eq!(worker.best_beefy_block(), 1);
		poll_fn(move |cx| {
			// unknown hash -> nothing streamed
			assert_eq!(best_block_stream.poll_next_unpin(cx), Poll::Pending);
			// commitment streamed
			match finality_proof.poll_next_unpin(cx) {
				// expect justification
				Poll::Ready(Some(received)) => assert_eq!(received, justif),
				v => panic!("unexpected value: {:?}", v),
			}
			Poll::Ready(())
		})
		.await;

		// generate 2 blocks, try again expect success
		let (mut best_block_streams, _) = get_beefy_streams(&mut net, keys);
		let mut best_block_stream = best_block_streams.drain(..).next().unwrap();
		let hashes = net.peer(0).push_blocks(2, false);
		// finalize 1 and 2 without justifications (hashes does not contain genesis)
		let hashof1 = hashes[0];
		let hashof2 = hashes[1];
		backend.finalize_block(hashof1, None).unwrap();
		backend.finalize_block(hashof2, None).unwrap();

		let justif = create_finality_proof(2);
		// create new session at block #2
		worker.persisted_state.voting_oracle.add_session(Rounds::new(2, validator_set));
		worker.finalize(justif).unwrap();
		// verify old session pruned
		assert_eq!(worker.voting_oracle().sessions.len(), 1);
		// new session starting at #2 is in front
		assert_eq!(worker.active_rounds().unwrap().session_start(), 2);
		// verify block finalized
		assert_eq!(worker.best_beefy_block(), 2);
		poll_fn(move |cx| {
			match best_block_stream.poll_next_unpin(cx) {
				// expect Some(hash-of-block-2)
				Poll::Ready(Some(hash)) => {
					let block_num = net.peer(0).client().as_client().number(hash).unwrap();
					assert_eq!(block_num, Some(2));
				},
				v => panic!("unexpected value: {:?}", v),
			}
			Poll::Ready(())
		})
		.await;

		// check BEEFY justifications are also appended to backend
		let justifs = backend.blockchain().justifications(hashof2).unwrap().unwrap();
		assert!(justifs.get(BEEFY_ENGINE_ID).is_some())
	}

	#[tokio::test]
	async fn should_init_session() {
		let keys = &[Keyring::Alice, Keyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1, validator_set.clone());

		let worker_rounds = worker.active_rounds().unwrap();
		assert_eq!(worker_rounds.session_start(), 1);
		assert_eq!(worker_rounds.validators(), validator_set.validators());
		assert_eq!(worker_rounds.validator_set_id(), validator_set.id());

		// new validator set
		let keys = &[Keyring::Bob];
		let new_validator_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();

		worker.init_session_at(new_validator_set.clone(), 11);
		// Since mandatory is not done for old rounds, we still get those.
		let rounds = worker.persisted_state.voting_oracle.active_rounds_mut().unwrap();
		assert_eq!(rounds.validator_set_id(), validator_set.id());
		// Let's finalize mandatory.
		rounds.test_set_mandatory_done(true);
		worker.persisted_state.voting_oracle.try_prune();
		// Now we should get the next round.
		let rounds = worker.active_rounds().unwrap();
		// Expect new values.
		assert_eq!(rounds.session_start(), 11);
		assert_eq!(rounds.validators(), new_validator_set.validators());
		assert_eq!(rounds.validator_set_id(), new_validator_set.id());
	}

	#[tokio::test]
	async fn should_triage_votes_and_process_later() {
		let keys = &[Keyring::Alice, Keyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let mut net = BeefyTestNet::new(1);
		let mut worker = create_beefy_worker(&net.peer(0), &keys[0], 1, validator_set.clone());
		// remove default session, will manually add custom one.
		worker.persisted_state.voting_oracle.sessions.clear();

		fn new_vote(
			block_number: NumberFor<Block>,
		) -> VoteMessage<NumberFor<Block>, AuthorityId, Signature> {
			let commitment = Commitment {
				payload: Payload::from_single_entry(*b"BF", vec![]),
				block_number,
				validator_set_id: 0,
			};
			VoteMessage {
				commitment,
				id: Keyring::Alice.public(),
				signature: Keyring::Alice.sign(b"I am committed"),
			}
		}

		// best grandpa is 20
		let best_grandpa_header = Header::new(
			20u32.into(),
			Default::default(),
			Default::default(),
			Default::default(),
			Digest::default(),
		);

		worker
			.persisted_state
			.voting_oracle
			.add_session(Rounds::new(10, validator_set.clone()));
		worker.persisted_state.best_grandpa_block_header = best_grandpa_header;

		// triage votes for blocks 10..13
		worker.triage_incoming_vote(new_vote(10)).unwrap();
		worker.triage_incoming_vote(new_vote(11)).unwrap();
		worker.triage_incoming_vote(new_vote(12)).unwrap();
		// triage votes for blocks 20..23
		worker.triage_incoming_vote(new_vote(20)).unwrap();
		worker.triage_incoming_vote(new_vote(21)).unwrap();
		worker.triage_incoming_vote(new_vote(22)).unwrap();

		// vote for 10 should have been handled, while the rest buffered for later processing
		let mut votes = worker.pending_votes.values();
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 11);
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 12);
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 20);
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 21);
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 22);
		assert!(votes.next().is_none());

		// simulate mandatory done, and retry buffered votes
		worker
			.persisted_state
			.voting_oracle
			.active_rounds_mut()
			.unwrap()
			.test_set_mandatory_done(true);
		worker.try_pending_justif_and_votes().unwrap();
		// all blocks <= grandpa finalized should have been handled, rest still buffered
		let mut votes = worker.pending_votes.values();
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 21);
		assert_eq!(votes.next().unwrap().first().unwrap().commitment.block_number, 22);
	}
}
