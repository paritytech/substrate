// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Propagation and agreement of candidates.
//!
//! Authorities are split into groups by parachain, and each authority might come
//! up its own candidate for their parachain. Within groups, authorities pass around
//! their candidates and produce statements of validity.
//!
//! Any candidate that receives majority approval by the authorities in a group
//! may be subject to inclusion, unless any authorities flag that candidate as invalid.
//!
//! Wrongly flagging as invalid should be strongly disincentivized, so that in the
//! equilibrium state it is not expected to happen. Likewise with the submission
//! of invalid blocks.
//!
//! Groups themselves may be compromised by malicious authorities.

extern crate ed25519;
extern crate parking_lot;
extern crate polkadot_api;
extern crate polkadot_collator as collator;
extern crate polkadot_statement_table as table;
extern crate polkadot_parachain as parachain;
extern crate polkadot_primitives;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_runtime;

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_network;

extern crate exit_future;
extern crate tokio_core;
extern crate substrate_client as client;

#[macro_use]
extern crate error_chain;

#[macro_use]
extern crate futures;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_keyring;

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use codec::Slicable;
use table::generic::Statement as GenericStatement;
use runtime_support::Hashable;
use polkadot_api::{PolkadotApi, BlockBuilder};
use polkadot_primitives::{Hash, Timestamp};
use polkadot_primitives::parachain::{Id as ParaId, Chain, DutyRoster, BlockData, Extrinsic, CandidateReceipt};
use primitives::block::{Block as SubstrateBlock, Header as SubstrateHeader, HeaderHash, Id as BlockId, Number as BlockNumber};
use primitives::AuthorityId;
use transaction_pool::{Ready, TransactionPool};
use tokio_core::reactor::{Handle, Timeout, Interval};

use futures::prelude::*;
use futures::future::{self, Shared};
use collation::CollationFetch;
use dynamic_inclusion::DynamicInclusion;

pub use self::collation::{Collators, Collation};
pub use self::error::{ErrorKind, Error};
pub use self::shared_table::{SharedTable, StatementSource, StatementProducer, ProducedStatements};
pub use service::Service;

mod collation;
mod dynamic_inclusion;
mod evaluation;
mod error;
mod service;
mod shared_table;

// block size limit.
const MAX_TRANSACTIONS_SIZE: usize = 4 * 1024 * 1024;

/// A handle to a statement table router.
///
/// This is expected to be a lightweight, shared type like an `Arc`.
pub trait TableRouter: Clone {
	/// Errors when fetching data from the network.
	type Error;
	/// Future that resolves when candidate data is fetched.
	type FetchCandidate: IntoFuture<Item=BlockData,Error=Self::Error>;
	/// Future that resolves when extrinsic candidate data is fetched.
	type FetchExtrinsic: IntoFuture<Item=Extrinsic,Error=Self::Error>;

	/// Note local candidate data, making it available on the network to other validators.
	fn local_candidate_data(&self, hash: Hash, block_data: BlockData, extrinsic: Extrinsic);

	/// Fetch block data for a specific candidate.
	fn fetch_block_data(&self, candidate: &CandidateReceipt) -> Self::FetchCandidate;

	/// Fetch extrinsic data for a specific candidate.
	fn fetch_extrinsic_data(&self, candidate: &CandidateReceipt) -> Self::FetchExtrinsic;
}

/// A long-lived network which can create statement table routing instances.
pub trait Network {
	/// The table router type. This should handle importing of any statements,
	/// routing statements to peers, and driving completion of any `StatementProducers`.
	type TableRouter: TableRouter;

	/// Instantiate a table router using the given shared table.
	fn table_router(&self, table: Arc<SharedTable>) -> Self::TableRouter;
}

/// Information about a specific group.
#[derive(Debug, Clone, Default)]
pub struct GroupInfo {
	/// Authorities meant to check validity of candidates.
	pub validity_guarantors: HashSet<AuthorityId>,
	/// Authorities meant to check availability of candidate data.
	pub availability_guarantors: HashSet<AuthorityId>,
	/// Number of votes needed for validity.
	pub needed_validity: usize,
	/// Number of votes needed for availability.
	pub needed_availability: usize,
}

/// Sign a table statement against a parent hash.
/// The actual message signed is the encoded statement concatenated with the
/// parent hash.
pub fn sign_table_statement(statement: &table::Statement, key: &ed25519::Pair, parent_hash: &Hash) -> ed25519::Signature {
	use polkadot_primitives::parachain::Statement as RawStatement;

	let raw = match *statement {
		GenericStatement::Candidate(ref c) => RawStatement::Candidate(c.clone()),
		GenericStatement::Valid(h) => RawStatement::Valid(h),
		GenericStatement::Invalid(h) => RawStatement::Invalid(h),
		GenericStatement::Available(h) => RawStatement::Available(h),
	};

	let mut encoded = raw.encode();
	encoded.extend(&parent_hash.0);

	key.sign(&encoded)
}

fn make_group_info(roster: DutyRoster, authorities: &[AuthorityId], local_id: AuthorityId) -> Result<(HashMap<ParaId, GroupInfo>, LocalDuty), Error> {
	if roster.validator_duty.len() != authorities.len() {
		bail!(ErrorKind::InvalidDutyRosterLength(authorities.len(), roster.validator_duty.len()))
	}

	if roster.guarantor_duty.len() != authorities.len() {
		bail!(ErrorKind::InvalidDutyRosterLength(authorities.len(), roster.guarantor_duty.len()))
	}

	let mut local_validation = None;
	let mut map = HashMap::new();

	let duty_iter = authorities.iter().zip(&roster.validator_duty).zip(&roster.guarantor_duty);
	for ((authority, v_duty), a_duty) in duty_iter {
		if authority == &local_id {
			local_validation = Some(v_duty.clone());
		}

		match *v_duty {
			Chain::Relay => {}, // does nothing for now.
			Chain::Parachain(ref id) => {
				map.entry(id.clone()).or_insert_with(GroupInfo::default)
					.validity_guarantors
					.insert(authority.clone());
			}
		}

		match *a_duty {
			Chain::Relay => {}, // does nothing for now.
			Chain::Parachain(ref id) => {
				map.entry(id.clone()).or_insert_with(GroupInfo::default)
					.availability_guarantors
					.insert(authority.clone());
			}
		}
	}

	for live_group in map.values_mut() {
		let validity_len = live_group.validity_guarantors.len();
		let availability_len = live_group.availability_guarantors.len();

		live_group.needed_validity = validity_len / 2 + validity_len % 2;
		live_group.needed_availability = availability_len / 2 + availability_len % 2;
	}

	match local_validation {
		Some(local_validation) => {
			let local_duty = LocalDuty {
				validation: local_validation,
			};

			Ok((map, local_duty))
		}
		None => bail!(ErrorKind::NotValidator(local_id)),
	}
}

fn timer_error(e: &::std::io::Error) -> Error {
	ErrorKind::Timer(format!("{}", e)).into()
}

/// Polkadot proposer factory.
pub struct ProposerFactory<C, N, P> {
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool>,
	/// The backing network handle.
	pub network: N,
	/// Parachain collators.
	pub collators: P,
	/// The timer used to schedule proposal intervals.
	pub handle: Handle,
	/// The duration after which parachain-empty blocks will be allowed.
	pub parachain_empty_duration: Duration,
}

impl<C, N, P> bft::ProposerFactory for ProposerFactory<C, N, P>
	where
		C: PolkadotApi,
		N: Network,
		P: Collators,
{
	type Proposer = Proposer<C, N::TableRouter, P>;
	type Error = Error;

	fn init(&self, parent_header: &SubstrateHeader, authorities: &[AuthorityId], sign_with: Arc<ed25519::Pair>) -> Result<Self::Proposer, Error> {
		use std::time::Duration;

		const DELAY_UNTIL: Duration = Duration::from_millis(5000);

		let parent_hash = parent_header.blake2_256().into();

		let checked_id = self.client.check_id(BlockId::Hash(parent_hash))?;
		let duty_roster = self.client.duty_roster(&checked_id)?;
		let random_seed = self.client.random_seed(&checked_id)?;

		let (group_info, local_duty) = make_group_info(
			duty_roster,
			authorities,
			sign_with.public().0,
		)?;

		let active_parachains = self.client.active_parachains(&checked_id)?;

		let n_parachains = active_parachains.len();
		let table = Arc::new(SharedTable::new(group_info, sign_with.clone(), parent_hash));
		let router = self.network.table_router(table.clone());
		let dynamic_inclusion = DynamicInclusion::new(
			n_parachains,
			Instant::now(),
			self.parachain_empty_duration.clone(),
		);

		let timeout = Timeout::new(DELAY_UNTIL, &self.handle)
			.map_err(|e| timer_error(&e))?;

		debug!(target: "bft", "Initialising consensus proposer. Refusing to evaluate for {:?} from now.",
			DELAY_UNTIL);

		// TODO [PoC-2]: kick off collation process.
		Ok(Proposer {
			client: self.client.clone(),
			collators: self.collators.clone(),
			delay: timeout.shared(),
			handle: self.handle.clone(),
			dynamic_inclusion,
			local_duty,
			local_key: sign_with,
			parent_hash,
			parent_id: checked_id,
			parent_number: parent_header.number,
			random_seed,
			router,
			table,
			transaction_pool: self.transaction_pool.clone(),
		})
	}
}

struct LocalDuty {
	validation: Chain,
}

/// The Polkadot proposer logic.
pub struct Proposer<C: PolkadotApi, R, P> {
	client: Arc<C>,
	collators: P,
	delay: Shared<Timeout>,
	dynamic_inclusion: DynamicInclusion,
	handle: Handle,
	local_duty: LocalDuty,
	local_key: Arc<ed25519::Pair>,
	parent_hash: HeaderHash,
	parent_id: C::CheckedBlockId,
	parent_number: BlockNumber,
	random_seed: Hash,
	router: R,
	table: Arc<SharedTable>,
	transaction_pool: Arc<TransactionPool>,
}

impl<C, R, P> bft::Proposer for Proposer<C, R, P>
	where
		C: PolkadotApi,
		R: TableRouter,
		P: Collators,
{
	type Error = Error;
	type Create = future::Either<
		CreateProposal<C, R, P>,
		future::FutureResult<SubstrateBlock, Error>,
	>;
	type Evaluate = Box<Future<Item=bool, Error=Error>>;

	fn propose(&self) -> Self::Create {
		const ATTEMPT_PROPOSE_EVERY: Duration = Duration::from_millis(100);

		let initial_included = self.table.includable_count();
		let enough_candidates = self.dynamic_inclusion.acceptable_in(
			Instant::now(),
			initial_included,
		).unwrap_or_default();

		let timing = {
			let delay = self.delay.clone();
			let dynamic_inclusion = self.dynamic_inclusion.clone();
			let make_timing = move |handle| -> Result<ProposalTiming, ::std::io::Error> {
				let attempt_propose = Interval::new(ATTEMPT_PROPOSE_EVERY, handle)?;
				let enough_candidates = Timeout::new(enough_candidates, handle)?;
				Ok(ProposalTiming {
					attempt_propose,
					enough_candidates,
					dynamic_inclusion,
					minimum_delay: Some(delay),
					last_included: initial_included,
				})
			};

			match make_timing(&self.handle) {
				Ok(timing) => timing,
				Err(e) => {
					return future::Either::B(future::err(timer_error(&e)));
				}
			}
		};

		future::Either::A(CreateProposal {
			parent_hash: self.parent_hash.clone(),
			parent_number: self.parent_number.clone(),
			parent_id: self.parent_id.clone(),
			client: self.client.clone(),
			transaction_pool: self.transaction_pool.clone(),
			collation: CollationFetch::new(
				self.local_duty.validation,
				self.parent_id.clone(),
				self.parent_hash.clone(),
				self.collators.clone(),
				self.client.clone()
			),
			table: self.table.clone(),
			router: self.router.clone(),
			timing,
		})
	}

	fn evaluate(&self, proposal: &SubstrateBlock) -> Self::Evaluate {
		debug!(target: "bft", "evaluating block on top of parent ({}, {:?})", self.parent_number, self.parent_hash);

		let active_parachains = match self.client.active_parachains(&self.parent_id) {
			Ok(x) => x,
			Err(e) => return Box::new(future::err(e.into())) as Box<_>,
		};

		let current_timestamp = current_timestamp();

		// do initial serialization and structural integrity checks.
		let maybe_proposal = evaluation::evaluate_initial(
			proposal,
			current_timestamp,
			&self.parent_hash,
			self.parent_number,
			&active_parachains,
		);

		let proposal = match maybe_proposal {
			Ok(p) => p,
			Err(e) => {
				// TODO: these errors are easily re-checked in runtime.
				debug!(target: "bft", "Invalid proposal: {:?}", e);
				return Box::new(future::ok(false));
			}
		};

		let vote_delays = {
			// delay casting vote until able (according to minimum block time)
			let minimum_delay = self.delay.clone()
				.map_err(|e| timer_error(&*e));

			let included_candidate_hashes = proposal
				.parachain_heads()
				.iter()
				.map(|candidate| candidate.hash());

			// delay casting vote until we have proof that all candidates are
			// includable.
			let includability_tracker = self.table.track_includability(included_candidate_hashes)
				.map_err(|_| ErrorKind::PrematureDestruction.into());

			// the duration at which the given number of parachains is acceptable.
			let count_delay = self.dynamic_inclusion.acceptable_in(
				Instant::now(),
				proposal.parachain_heads().len(),
			);

			// the duration until the given timestamp is current
			let proposed_timestamp = proposal.timestamp();
			let timestamp_delay = if proposed_timestamp > current_timestamp {
				Some(Duration::from_secs(proposed_timestamp - current_timestamp))
			} else {
				None
			};

			// construct a future from the maximum of the two durations.
			let temporary_delay = match ::std::cmp::max(timestamp_delay, count_delay) {
				Some(duration) => {
					let maybe_timeout = Timeout::new(duration, &self.handle);

					let f = future::result(maybe_timeout)
						.and_then(|timeout| timeout)
						.map_err(|e| timer_error(&e));

					future::Either::A(f)
				}
				None => future::Either::B(future::ok(())),
			};

			minimum_delay.join3(includability_tracker, temporary_delay)
		};

		// evaluate whether the block is actually valid.
		// TODO: is it better to delay this until the delays are finished?
		let evaluated = self.client.evaluate_block(&self.parent_id, proposal.into()).map_err(Into::into);
		let future = future::result(evaluated).and_then(move |good| {
			let end_result = future::ok(good);
			if good {
				// delay a "good" vote.
				future::Either::A(vote_delays.and_then(|_| end_result))
			} else {
				// don't delay a "bad" evaluation.
				future::Either::B(end_result)
			}
		});

		Box::new(future) as Box<_>
	}

	fn round_proposer(&self, round_number: usize, authorities: &[AuthorityId]) -> AuthorityId {
		use primitives::uint::U256;

		let len: U256 = authorities.len().into();
		let offset = U256::from_big_endian(&self.random_seed.0) % len;
		let offset = offset.low_u64() as usize + round_number;

		let proposer = authorities[offset % authorities.len()].clone();
		trace!(target: "bft", "proposer for round {} is {}", round_number, Hash::from(proposer));

		proposer
	}

	fn import_misbehavior(&self, misbehavior: Vec<(AuthorityId, bft::Misbehavior)>) {
		use bft::generic::Misbehavior as GenericMisbehavior;
		use primitives::bft::{MisbehaviorKind, MisbehaviorReport};
		use polkadot_runtime::{Call, Extrinsic, UncheckedExtrinsic, ConsensusCall};


		let local_id = self.local_key.public().0;
		let mut next_index = {
			let readiness_evaluator = Ready::create(self.parent_id.clone(), &*self.client);
			let cur_index = self.transaction_pool.cull_and_get_pending(readiness_evaluator, |pending| pending
				.filter(|tx| tx.as_ref().as_ref().signed == local_id)
				.last()
				.map(|tx| Ok(tx.as_ref().as_ref().index))
				.unwrap_or_else(|| self.client.index(&self.parent_id, local_id))
			);

			match cur_index {
				Ok(cur_index) => cur_index + 1,
				Err(e) => {
					warn!(target: "consensus", "Error computing next transaction index: {}", e);
					return;
				}
			}
		};

		for (target, misbehavior) in misbehavior {
			let report = MisbehaviorReport {
				parent_hash: self.parent_hash,
				parent_number: self.parent_number,
				target,
				misbehavior: match misbehavior {
					GenericMisbehavior::ProposeOutOfTurn(_, _, _) => continue,
					GenericMisbehavior::DoublePropose(_, _, _) => continue,
					GenericMisbehavior::DoublePrepare(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoublePrepare(round as u32, (h1, s1.signature), (h2, s2.signature)),
					GenericMisbehavior::DoubleCommit(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoubleCommit(round as u32, (h1, s1.signature), (h2, s2.signature)),
				}
			};
			let extrinsic = Extrinsic {
				signed: local_id,
				index: next_index,
				function: Call::Consensus(ConsensusCall::report_misbehavior(report)),
			};

			next_index += 1;

			let signature = self.local_key.sign(&extrinsic.encode()).into();
			let uxt = UncheckedExtrinsic { extrinsic, signature };

			self.transaction_pool.import_unchecked_extrinsic(uxt).expect("locally signed extrinsic is valid; qed");
		}
	}
}

fn current_timestamp() -> Timestamp {
	use std::time;

	time::SystemTime::now().duration_since(time::UNIX_EPOCH)
		.expect("now always later than unix epoch; qed")
		.as_secs()
}

struct ProposalTiming {
	attempt_propose: Interval,
	dynamic_inclusion: DynamicInclusion,
	enough_candidates: Timeout,
	minimum_delay: Option<Shared<Timeout>>,
	last_included: usize,
}

impl ProposalTiming {
	// whether it's time to attempt a proposal.
	// shouldn't be called outside of the context of a task.
	fn poll(&mut self, included: usize) -> Poll<(), Error> {
		// first drain from the interval so when the minimum delay is up
		// we don't have any notifications built up.
		//
		// this interval is just meant to produce periodic task wakeups
		// that lead to the `dynamic_inclusion` getting updated as necessary.
		if let Async::Ready(x) = self.attempt_propose.poll()
			.map_err(|e| timer_error(&e))?
		{
			x.expect("timer still alive; intervals never end; qed");
		}

		if let Some(ref mut min) = self.minimum_delay {
			try_ready!(min.poll().map_err(|e| timer_error(&*e)));
		}

		self.minimum_delay = None; // after this point, the future must have completed.

		if included == self.last_included {
			return self.enough_candidates.poll().map_err(|e| timer_error(&e));
		}

		// the amount of includable candidates has changed. schedule a wakeup
		// if it's not sufficient anymore.
		let now = Instant::now();
		match self.dynamic_inclusion.acceptable_in(now, included) {
			Some(duration) => {
				self.last_included = included;
				self.enough_candidates.reset(now + duration);
				self.enough_candidates.poll().map_err(|e| timer_error(&e))
			}
			None => {
				Ok(Async::Ready(()))
			}
		}
	}
}

/// Future which resolves upon the creation of a proposal.
pub struct CreateProposal<C: PolkadotApi, R, P: Collators>  {
	parent_hash: HeaderHash,
	parent_number: BlockNumber,
	parent_id: C::CheckedBlockId,
	client: Arc<C>,
	transaction_pool: Arc<TransactionPool>,
	collation: CollationFetch<P, C>,
	router: R,
	table: Arc<SharedTable>,
	timing: ProposalTiming,
}

impl<C, R, P> CreateProposal<C, R, P>
	where
		C: PolkadotApi,
		R: TableRouter,
		P: Collators,
{
	fn propose_with(&self, candidates: Vec<CandidateReceipt>) -> Result<SubstrateBlock, Error> {
		// TODO: handle case when current timestamp behind that in state.
		let timestamp = current_timestamp();
		let mut block_builder = self.client.build_block(
			&self.parent_id,
			timestamp,
			candidates,
		)?;

		{
			let readiness_evaluator = Ready::create(self.parent_id.clone(), &*self.client);
			let mut unqueue_invalid = Vec::new();
			self.transaction_pool.cull_and_get_pending(readiness_evaluator, |pending_iterator| {
				let mut pending_size = 0;
				for pending in pending_iterator {
					// skip and cull transactions which are too large.
					if pending.encoded_size() > MAX_TRANSACTIONS_SIZE {
						unqueue_invalid.push(pending.hash().clone());
						continue
					}

					if pending_size + pending.encoded_size() >= MAX_TRANSACTIONS_SIZE { break }

					match block_builder.push_extrinsic(pending.as_transaction().clone()) {
						Ok(()) => {
							pending_size += pending.encoded_size();
						}
						Err(e) => {
							trace!(target: "transaction-pool", "Invalid transaction: {}", e);
							unqueue_invalid.push(pending.hash().clone());
						}
					}
				}
			});

			self.transaction_pool.remove(&unqueue_invalid, false);
		}

		let polkadot_block = block_builder.bake();

		info!("Proposing block [number: {}; hash: {}; parent_hash: {}; extrinsics: [{}]]",
			polkadot_block.header.number,
			Hash::from(polkadot_block.header.blake2_256()),
			polkadot_block.header.parent_hash,
			polkadot_block.extrinsics.iter()
				.map(|xt| format!("{}", Hash::from(xt.blake2_256())))
				.collect::<Vec<_>>()
				.join(", ")
		);

		let substrate_block = Slicable::decode(&mut polkadot_block.encode().as_slice())
			.expect("polkadot blocks defined to serialize to substrate blocks correctly; qed");

		// TODO: full re-evaluation
		let active_parachains = self.client.active_parachains(&self.parent_id)?;
		assert!(evaluation::evaluate_initial(
			&substrate_block,
			timestamp,
			&self.parent_hash,
			self.parent_number,
			&active_parachains,
		).is_ok());

		Ok(substrate_block)
	}
}

impl<C, R, P> Future for CreateProposal<C, R, P>
	where
		C: PolkadotApi,
		R: TableRouter,
		P: Collators,
{
	type Item = SubstrateBlock;
	type Error = Error;

	fn poll(&mut self) -> Poll<SubstrateBlock, Error> {
		// 1. poll local collation future.
		match self.collation.poll() {
			Ok(Async::Ready((collation, extrinsic))) => {
				let hash = collation.receipt.hash();
				self.router.local_candidate_data(hash, collation.block_data, extrinsic);

				// TODO: if we are an availability guarantor also, we should produce an availability statement.
				self.table.sign_and_import(&self.router, GenericStatement::Candidate(collation.receipt));
			}
			Ok(Async::NotReady) => {},
			Err(_) => {}, // TODO: handle this failure to collate.
		}

		// 2. try to propose if we have enough includable candidates and other
		// delays have concluded.
		let included = self.table.includable_count();
		try_ready!(self.timing.poll(included));

		// 3. propose
		let proposed_candidates = self.table.with_proposal(|proposed_set| {
			proposed_set.into_iter().cloned().collect()
		});

		self.propose_with(proposed_candidates).map(Async::Ready)
	}
}
