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
extern crate polkadot_statement_table as table;
extern crate polkadot_parachain as parachain;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_runtime;
extern crate polkadot_primitives;

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_client as client;

extern crate exit_future;
extern crate tokio;

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
use polkadot_api::PolkadotApi;
use polkadot_primitives::{Hash, Block, BlockId, BlockNumber, Header, Timestamp, SessionKey};
use polkadot_primitives::parachain::{Id as ParaId, Chain, DutyRoster, BlockData, Extrinsic as ParachainExtrinsic, CandidateReceipt, CandidateSignature};
use primitives::AuthorityId;
use transaction_pool::TransactionPool;
use tokio::runtime::TaskExecutor;
use tokio::timer::{Delay, Interval};

use futures::prelude::*;
use futures::future;
use collation::CollationFetch;
use dynamic_inclusion::DynamicInclusion;

pub use self::collation::{validate_collation, Collators};
pub use self::error::{ErrorKind, Error};
pub use self::shared_table::{SharedTable, StatementProducer, ProducedStatements, Statement, SignedStatement, GenericStatement};
pub use service::Service;

mod dynamic_inclusion;
mod evaluation;
mod error;
mod service;
mod shared_table;

pub mod collation;

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
	type FetchExtrinsic: IntoFuture<Item=ParachainExtrinsic,Error=Self::Error>;

	/// Call with local candidate data. This will make the data available on the network,
	/// and sign, import, and broadcast a statement about the candidate.
	fn local_candidate(&self, candidate: CandidateReceipt, block_data: BlockData, extrinsic: ParachainExtrinsic);

	/// Fetch block data for a specific candidate.
	fn fetch_block_data(&self, candidate: &CandidateReceipt) -> Self::FetchCandidate;

	/// Fetch extrinsic data for a specific candidate.
	fn fetch_extrinsic_data(&self, candidate: &CandidateReceipt) -> Self::FetchExtrinsic;
}

/// A long-lived network which can create parachain statement and BFT message routing processes on demand.
pub trait Network {
	/// The table router type. This should handle importing of any statements,
	/// routing statements to peers, and driving completion of any `StatementProducers`.
	type TableRouter: TableRouter;
	/// The input stream of BFT messages. Should never logically conclude.
	type Input: Stream<Item=bft::Communication<Block>,Error=Error>;
	/// The output sink of BFT messages. Messages sent here should eventually pass to all
	/// current authorities.
	type Output: Sink<SinkItem=bft::Communication<Block>,SinkError=Error>;

	/// Instantiate a table router using the given shared table and task executor.
	fn communication_for(&self, validators: &[SessionKey], table: Arc<SharedTable>, task_executor: TaskExecutor) -> (Self::TableRouter, Self::Input, Self::Output);
}

/// Information about a specific group.
#[derive(Debug, Clone, Default)]
pub struct GroupInfo {
	/// Authorities meant to check validity of candidates.
	pub validity_guarantors: HashSet<SessionKey>,
	/// Authorities meant to check availability of candidate data.
	pub availability_guarantors: HashSet<SessionKey>,
	/// Number of votes needed for validity.
	pub needed_validity: usize,
	/// Number of votes needed for availability.
	pub needed_availability: usize,
}

/// Sign a table statement against a parent hash.
/// The actual message signed is the encoded statement concatenated with the
/// parent hash.
pub fn sign_table_statement(statement: &Statement, key: &ed25519::Pair, parent_hash: &Hash) -> CandidateSignature {
	let mut encoded = statement.encode();
	encoded.extend(&parent_hash.0);

	key.sign(&encoded).into()
}

/// Check signature on table statement.
pub fn check_statement(statement: &Statement, signature: &CandidateSignature, signer: SessionKey, parent_hash: &Hash) -> bool {
	use runtime_primitives::traits::Verify;

	let mut encoded = statement.encode();
	encoded.extend(&parent_hash.0);

	signature.verify(&encoded[..], &signer.into())
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

/// Polkadot proposer factory.
pub struct ProposerFactory<C, N, P> {
	/// The client instance.
	pub client: Arc<P>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool<P>>,
	/// The backing network handle.
	pub network: N,
	/// Parachain collators.
	pub collators: C,
	/// handle to remote task executor
	pub handle: TaskExecutor,
	/// The duration after which parachain-empty blocks will be allowed.
	pub parachain_empty_duration: Duration,
}

impl<C, N, P> bft::Environment<Block> for ProposerFactory<C, N, P>
	where
		C: Collators + Send + 'static,
		N: Network,
		P: PolkadotApi + Send + Sync + 'static,
		<C::Collation as IntoFuture>::Future: Send + 'static,
		N::TableRouter: Send + 'static,
{
	type Proposer = Proposer<P>;
	type Input = N::Input;
	type Output = N::Output;
	type Error = Error;

	fn init(&self,
		parent_header: &Header,
		authorities: &[AuthorityId],
		sign_with: Arc<ed25519::Pair>
	) -> Result<(Self::Proposer, Self::Input, Self::Output), Error> {
		const DELAY_UNTIL: Duration = Duration::from_millis(5000);

		let parent_hash = parent_header.hash().into();

		let id = BlockId::hash(parent_hash);
		let duty_roster = self.client.duty_roster(&id)?;
		let random_seed = self.client.random_seed(&id)?;

		let (group_info, local_duty) = make_group_info(
			duty_roster,
			authorities,
			sign_with.public().into(),
		)?;

		let active_parachains = self.client.active_parachains(&id)?;

		let n_parachains = active_parachains.len();
		let table = Arc::new(SharedTable::new(group_info, sign_with.clone(), parent_hash));
		let (router, input, output) = self.network.communication_for(
			authorities,
			table.clone(),
			self.handle.clone()
		);

		let now = Instant::now();
		let dynamic_inclusion = DynamicInclusion::new(
			n_parachains,
			now,
			self.parachain_empty_duration.clone(),
		);

		debug!(target: "bft", "Initialising consensus proposer. Refusing to evaluate for {:?} from now.",
			DELAY_UNTIL);

		let validation_para = match local_duty.validation {
			Chain::Relay => None,
			Chain::Parachain(id) => Some(id),
		};

		let collation_work = validation_para.map(|para| CollationFetch::new(
			para,
			id.clone(),
			parent_hash.clone(),
			self.collators.clone(),
			self.client.clone(),
		));
		let drop_signal = dispatch_collation_work(
			router.clone(),
			&self.handle,
			collation_work,
		);

		let proposer = Proposer {
			client: self.client.clone(),
			dynamic_inclusion,
			local_key: sign_with,
			minimum_delay: now + DELAY_UNTIL,
			parent_hash,
			parent_id: id,
			parent_number: parent_header.number,
			random_seed,
			table,
			transaction_pool: self.transaction_pool.clone(),
			_drop_signal: drop_signal,
		};

		Ok((proposer, input, output))
	}
}

// dispatch collation work to be done in the background. returns a signal object
// that should fire when the collation work is no longer necessary (e.g. when the proposer object is dropped)
fn dispatch_collation_work<R, C, P>(
	router: R,
	handle: &TaskExecutor,
	work: Option<CollationFetch<C, P>>,
) -> exit_future::Signal where
	C: Collators + Send + 'static,
	P: PolkadotApi + Send + Sync + 'static,
	<C::Collation as IntoFuture>::Future: Send + 'static,
	R: TableRouter + Send + 'static,
{
	let (signal, exit) = exit_future::signal();
	let handled_work = work.then(move |result| match result {
		Ok(Some((collation, extrinsic))) => {
			router.local_candidate(collation.receipt, collation.block_data, extrinsic);
			Ok(())
		}
		Ok(None) => Ok(()),
		Err(_e) => {
			warn!(target: "consensus", "Failed to collate candidate");
			Ok(())
		}
	});

	let cancellable_work = handled_work.select(exit).then(|_| Ok(()));

	// spawn onto thread pool.
	handle.spawn(cancellable_work);
	signal
}

struct LocalDuty {
	validation: Chain,
}

/// The Polkadot proposer logic.
pub struct Proposer<C: PolkadotApi> {
	client: Arc<C>,
	dynamic_inclusion: DynamicInclusion,
	local_key: Arc<ed25519::Pair>,
	minimum_delay: Instant,
	parent_hash: Hash,
	parent_id: BlockId,
	parent_number: BlockNumber,
	random_seed: Hash,
	table: Arc<SharedTable>,
	transaction_pool: Arc<TransactionPool<C>>,
	_drop_signal: exit_future::Signal,
}

impl<C> bft::Proposer<Block> for Proposer<C>
	where
		C: PolkadotApi + Send + Sync,
{
	type Error = Error;
	type Create = future::Either<
		CreateProposal<C>,
		future::FutureResult<Block, Error>,
	>;
	type Evaluate = Box<Future<Item=bool, Error=Error>>;

	fn propose(&self) -> Self::Create {
		const ATTEMPT_PROPOSE_EVERY: Duration = Duration::from_millis(100);

		let initial_included = self.table.includable_count();
		let now = Instant::now();
		let enough_candidates = self.dynamic_inclusion.acceptable_in(
			now,
			initial_included,
		).unwrap_or_else(|| now + Duration::from_millis(1));

		let minimum_delay = if self.minimum_delay > now + ATTEMPT_PROPOSE_EVERY {
			Some(Delay::new(self.minimum_delay))
		} else {
			None
		};

		let timing = ProposalTiming {
			attempt_propose: Interval::new(now + ATTEMPT_PROPOSE_EVERY, ATTEMPT_PROPOSE_EVERY),
			enough_candidates: Delay::new(enough_candidates),
			dynamic_inclusion: self.dynamic_inclusion.clone(),
			minimum_delay,
			last_included: initial_included,
		};

		future::Either::A(CreateProposal {
			parent_hash: self.parent_hash.clone(),
			parent_number: self.parent_number.clone(),
			parent_id: self.parent_id.clone(),
			client: self.client.clone(),
			transaction_pool: self.transaction_pool.clone(),
			table: self.table.clone(),
			timing,
		})
	}

	fn evaluate(&self, unchecked_proposal: &Block) -> Self::Evaluate {
		debug!(target: "bft", "evaluating block on top of parent ({}, {:?})", self.parent_number, self.parent_hash);

		let active_parachains = match self.client.active_parachains(&self.parent_id) {
			Ok(x) => x,
			Err(e) => return Box::new(future::err(e.into())) as Box<_>,
		};

		let current_timestamp = current_timestamp();

		// do initial serialization and structural integrity checks.
		let maybe_proposal = evaluation::evaluate_initial(
			unchecked_proposal,
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
			let now = Instant::now();

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
				now,
				proposal.parachain_heads().len(),
			);

			// the duration until the given timestamp is current
			let proposed_timestamp = proposal.timestamp();
			let timestamp_delay = if proposed_timestamp > current_timestamp {
				Some(now + Duration::from_secs(proposed_timestamp - current_timestamp))
			} else {
				None
			};

			// delay casting vote until able according to minimum block time,
			// timestamp delay, and count delay.
			// construct a future from the maximum of the two durations.
			let max_delay = [timestamp_delay, count_delay, Some(self.minimum_delay)]
				.iter()
				.cloned()
				.max()
				.expect("iterator not empty; thus max returns `Some`; qed");

			let temporary_delay = match max_delay {
				Some(duration) => future::Either::A(
					Delay::new(duration).map_err(|e| Error::from(ErrorKind::Timer(e)))
				),
				None => future::Either::B(future::ok(())),
			};

			includability_tracker.join(temporary_delay)
		};

		// evaluate whether the block is actually valid.
		// TODO: is it better to delay this until the delays are finished?
		let evaluated = self.client
			.evaluate_block(&self.parent_id, unchecked_proposal.clone())
			.map_err(Into::into);

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
		trace!(target: "bft", "proposer for round {} is {}", round_number, proposer);

		proposer
	}

	fn import_misbehavior(&self, misbehavior: Vec<(AuthorityId, bft::Misbehavior<Hash>)>) {
		use bft::generic::Misbehavior as GenericMisbehavior;
		use runtime_primitives::bft::{MisbehaviorKind, MisbehaviorReport};
		use runtime_primitives::MaybeUnsigned;
		use polkadot_runtime::{Call, Extrinsic, BareExtrinsic, UncheckedExtrinsic, ConsensusCall};

		let local_id = self.local_key.public().0.into();
		let mut next_index = {
			let cur_index = self.transaction_pool.cull_and_get_pending(BlockId::hash(self.parent_hash), |pending| pending
				.filter(|tx| tx.sender().map(|s| s == local_id).unwrap_or(false))
				.last()
				.map(|tx| Ok(tx.index()))
				.unwrap_or_else(|| self.client.index(&self.parent_id, local_id))
			);

			match cur_index {
				Ok(Ok(cur_index)) => cur_index + 1,
				Ok(Err(e)) => {
					warn!(target: "consensus", "Error computing next transaction index: {}", e);
					return;
				}
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
			let extrinsic = BareExtrinsic {
				signed: local_id,
				index: next_index,
				function: Call::Consensus(ConsensusCall::report_misbehavior(report)),
			};

			next_index += 1;

			let signature = MaybeUnsigned(self.local_key.sign(&extrinsic.encode()).into());

			let extrinsic = Extrinsic {
				signed: extrinsic.signed.into(),
				index: extrinsic.index,
				function: extrinsic.function,
			};
			let uxt = UncheckedExtrinsic::new(extrinsic, signature);

			self.transaction_pool.import_unchecked_extrinsic(BlockId::hash(self.parent_hash), uxt)
				.expect("locally signed extrinsic is valid; qed");
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
	enough_candidates: Delay,
	minimum_delay: Option<Delay>,
	last_included: usize,
}

impl ProposalTiming {
	// whether it's time to attempt a proposal.
	// shouldn't be called outside of the context of a task.
	fn poll(&mut self, included: usize) -> Poll<(), ErrorKind> {
		// first drain from the interval so when the minimum delay is up
		// we don't have any notifications built up.
		//
		// this interval is just meant to produce periodic task wakeups
		// that lead to the `dynamic_inclusion` getting updated as necessary.
		if let Async::Ready(x) = self.attempt_propose.poll().map_err(ErrorKind::Timer)? {
			x.expect("timer still alive; intervals never end; qed");
		}

		if let Some(ref mut min) = self.minimum_delay {
			try_ready!(min.poll().map_err(ErrorKind::Timer));
		}

		self.minimum_delay = None; // after this point, the future must have completed.

		if included == self.last_included {
			return self.enough_candidates.poll().map_err(ErrorKind::Timer);
		}

		// the amount of includable candidates has changed. schedule a wakeup
		// if it's not sufficient anymore.
		match self.dynamic_inclusion.acceptable_in(Instant::now(), included) {
			Some(instant) => {
				self.last_included = included;
				self.enough_candidates.reset(instant);
				self.enough_candidates.poll().map_err(ErrorKind::Timer)
			}
			None => Ok(Async::Ready(())),
		}
	}
}

/// Future which resolves upon the creation of a proposal.
pub struct CreateProposal<C: PolkadotApi>  {
	parent_hash: Hash,
	parent_number: BlockNumber,
	parent_id: BlockId,
	client: Arc<C>,
	transaction_pool: Arc<TransactionPool<C>>,
	table: Arc<SharedTable>,
	timing: ProposalTiming,
}

impl<C> CreateProposal<C> where C: PolkadotApi {
	fn propose_with(&self, candidates: Vec<CandidateReceipt>) -> Result<Block, Error> {
		use polkadot_api::BlockBuilder;
		use runtime_primitives::traits::{Hashing, BlakeTwo256};

		// TODO: handle case when current timestamp behind that in state.
		let timestamp = current_timestamp();
		let mut block_builder = self.client.build_block(&self.parent_id, timestamp, candidates)?;

		{
			let mut unqueue_invalid = Vec::new();
			let result = self.transaction_pool.cull_and_get_pending(BlockId::hash(self.parent_hash), |pending_iterator| {
				let mut pending_size = 0;
				for pending in pending_iterator {
					// skip and cull transactions which are too large.
					if pending.encoded_size() > MAX_TRANSACTIONS_SIZE {
						unqueue_invalid.push(pending.hash().clone());
						continue
					}

					if pending_size + pending.encoded_size() >= MAX_TRANSACTIONS_SIZE { break }

					match block_builder.push_extrinsic(pending.primitive_extrinsic()) {
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
			if let Err(e) = result {
				warn!("Unable to get the pending set: {:?}", e);
			}

			self.transaction_pool.remove(&unqueue_invalid, false);
		}

		let polkadot_block = block_builder.bake()?;

		info!("Proposing block [number: {}; hash: {}; parent_hash: {}; extrinsics: [{}]]",
			polkadot_block.header.number,
			Hash::from(polkadot_block.header.hash()),
			polkadot_block.header.parent_hash,
			polkadot_block.extrinsics.iter()
				.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
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

impl<C> Future for CreateProposal<C> where C: PolkadotApi {
	type Item = Block;
	type Error = Error;

	fn poll(&mut self) -> Poll<Block, Error> {
		// 1. try to propose if we have enough includable candidates and other
		// delays have concluded.
		let included = self.table.includable_count();
		try_ready!(self.timing.poll(included));

		// 2. propose
		let proposed_candidates = self.table.with_proposal(|proposed_set| {
			proposed_set.into_iter().cloned().collect()
		});

		self.propose_with(proposed_candidates).map(Async::Ready)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_keyring::Keyring;

	#[test]
	fn sign_and_check_statement() {
		let statement: Statement = GenericStatement::Valid([1; 32].into());
		let parent_hash = [2; 32].into();

		let sig = sign_table_statement(&statement, &Keyring::Alice.pair(), &parent_hash);

		assert!(check_statement(&statement, &sig, Keyring::Alice.to_raw_public().into(), &parent_hash));
		assert!(!check_statement(&statement, &sig, Keyring::Alice.to_raw_public().into(), &[0xff; 32].into()));
		assert!(!check_statement(&statement, &sig, Keyring::Bob.to_raw_public().into(), &parent_hash));
	}
}
