// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use crate::{self as multi_phase, unsigned as unsigned_pallet, verifier as verifier_pallet};
use frame_election_provider_support::{data_provider, ElectionDataProvider, Support};
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{parameter_types, traits::Hooks, weights::Weight};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, seq_phragmen, to_supports, to_without_backing,
	ElectionResult, EvaluateSupport, NposSolution,
};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16, Perbill,
};
use std::{convert::TryFrom, sync::Arc};

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, Call, (), ()>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>, Config},
		Balances: pallet_balances::{Pallet, Call, Event<T>, Config<T>},
		VerifierPallet: verifier_pallet::{Pallet},
		UnsignedPallet: unsigned_pallet::{Pallet, Call, ValidateUnsigned},
		MultiPhase: multi_phase::{Pallet, Call, Event<T>},
	}
);

pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;
pub(crate) type BlockNumber = u32;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestNposSolution::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

/// All events of this pallet.
pub(crate) fn multi_phase_events() -> Vec<super::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::MultiPhase(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

/// To from `now` to block `n`.
pub fn roll_to(n: u64) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiPhase::on_initialize(i);
	}
}

pub fn roll_to_with_ocw(n: u64) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiPhase::on_initialize(i);
		MultiPhase::offchain_worker(i);
	}
}

// pub struct TrimHelpers {
// 	pub voters: Vec<Voter<Runtime>>,
// 	pub assignments: Vec<IndexAssignmentOf<Runtime>>,
// 	pub encoded_size_of:
// 		Box<dyn Fn(&[IndexAssignmentOf<Runtime>]) -> Result<usize, sp_npos_elections::Error>>,
// 	pub voter_index: Box<
// 		dyn Fn(
// 			&<Runtime as frame_system::Config>::AccountId,
// 		) -> Option<SolutionVoterIndexOf<Runtime>>,
// 	>,
// }

/// Helpers for setting up trimming tests.
///
/// Assignments are pre-sorted in reverse order of stake.
// pub fn trim_helpers() -> TrimHelpers {
// 	let RoundSnapshot { voters, targets } = MultiPhase::snapshot().unwrap();
// 	let stakes: std::collections::HashMap<_, _> =
// 		voters.iter().map(|(id, stake, _)| (*id, *stake)).collect();

// 	// Compute the size of a solution comprised of the selected arguments.
// 	//
// 	// This function completes in `O(edges)`; it's expensive, but linear.
// 	let encoded_size_of = Box::new(|assignments: &[IndexAssignmentOf<Runtime>]| {
// 		SolutionOf::<Runtime>::try_from(assignments).map(|s| s.encoded_size())
// 	});
// 	let cache = helpers::generate_voter_cache::<Runtime>(&voters);
// 	let voter_index = helpers::voter_index_fn_owned::<Runtime>(cache);
// 	let target_index = helpers::target_index_fn::<Runtime>(&targets);

// 	let desired_targets = MultiPhase::desired_targets().unwrap();

// 	let ElectionResult { mut assignments, .. } = seq_phragmen::<_, SolutionAccuracyOf<Runtime>>(
// 		desired_targets as usize,
// 		targets.clone(),
// 		voters.clone(),
// 		None,
// 	)
// 	.unwrap();

// 	// sort by decreasing order of stake
// 	assignments.sort_unstable_by_key(|assignment| {
// 		std::cmp::Reverse(stakes.get(&assignment.who).cloned().unwrap_or_default())
// 	});

// 	// convert to IndexAssignment
// 	let assignments = assignments
// 		.iter()
// 		.map(|assignment| {
// 			IndexAssignmentOf::<Runtime>::new(assignment, &voter_index, &target_index)
// 		})
// 		.collect::<Result<Vec<_>, _>>()
// 		.expect("test assignments don't contain any voters with too many votes");

// 	TrimHelpers { voters, assignments, encoded_size_of, voter_index: Box::new(voter_index) }
// }

/// Creates a nested vec where the index of the first vec is the same as the key of the snapshot.
fn nested_voter_snapshot() -> Vec<Vec<Voter<Runtime>>> {
	let mut flatten: Vec<Vec<Voter<Runtime>>> = Vec::with_capacity(Pages::get() as usize);
	flatten.resize(Pages::get() as usize, vec![]);
	let voter_snapshot = <PagedVoterSnapshot<Runtime>>::iter().collect::<Vec<_>>();
	for (page, voters) in voter_snapshot {
		flatten[page as usize] = voters
	}

	flatten
}

pub fn raw_paged_solution() -> PagedRawSolution<SolutionOf<Runtime>> {
	// ensure snapshot exists.
	assert_eq!(<PagedTargetSnapshot<Runtime>>::iter().count(), 1);
	assert!(<PagedVoterSnapshot<Runtime>>::iter().count() > 0);

	// read all voter snapshots
	let voter_snapshot = nested_voter_snapshot();
	let target_snapshot = MultiPhase::paged_target_snapshot(0).unwrap();
	let desired_targets = MultiPhase::desired_targets().unwrap();

	let all_voters = voter_snapshot.iter().flatten().cloned().collect::<Vec<_>>();

	let ElectionResult { winners, assignments } = seq_phragmen::<_, SolutionAccuracyOf<Runtime>>(
		desired_targets as usize,
		target_snapshot.clone(),
		all_voters.clone(),
		None,
	)
	.unwrap();

	// compute score from the overall solution before dealing with pages in any way.
	let score = {
		let cache = helpers::generate_voter_cache::<Runtime>(&all_voters);
		let stake_of = helpers::stake_of_fn::<Runtime>(&all_voters, &cache);
		let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of).unwrap();
		let winners = to_without_backing(winners);
		to_supports::<AccountId>(&winners, &staked).unwrap().evaluate()
	};

	let page_for_voter = |voter: &AccountId| -> PageIndex {
		// TODO: for now we do this in a super naive way.
		voter_snapshot
			.iter()
			.enumerate()
			.find_map(|(page, voters)| {
				if voters.iter().find(|(x, _, _)| x == voter).is_some() {
					Some(page as PageIndex)
				} else {
					None
				}
			})
			.unwrap()
	};

	let mut paged_assignments: Vec<Vec<AssignmentOf<Runtime>>> =
		Vec::with_capacity(Pages::get() as usize);
	paged_assignments.resize(Pages::get() as usize, vec![]);
	for assignment in assignments {
		let page = page_for_voter(&assignment.who);
		paged_assignments[page as usize].push(assignment);
	}

	let target_index = helpers::target_index_fn_linear::<Runtime>(&target_snapshot);

	let mut solution_pages: Vec<SolutionOf<Runtime>> = Vec::with_capacity(Pages::get() as usize);
	for (index, assignment_page) in paged_assignments.iter().enumerate() {
		let corresponding_snapshot = &voter_snapshot[index];
		let voter_index = helpers::voter_index_fn_linear::<Runtime>(corresponding_snapshot);
		let page =
			<SolutionOf<Runtime>>::from_assignment(assignment_page, voter_index, &target_index)
				.unwrap();
		solution_pages.push(page);
	}

	let round = MultiPhase::round();

	PagedRawSolution { solution_pages, round, score }
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = BlockWeights;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub BlockWeights: frame_system::limits::BlockWeights = frame_system::limits::BlockWeights
		::with_sensible_defaults(2 * frame_support::weights::constants::WEIGHT_PER_SECOND, NORMAL_DISPATCH_RATIO);
}

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

parameter_types! {
	pub static Targets: Vec<AccountId> = vec![10, 20, 30, 40];
	pub static Voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)> = vec![
		(1, 10, vec![10, 20]),
		(2, 10, vec![30, 40]),
		(3, 10, vec![40]),
		(4, 10, vec![10, 20, 40]),
		(5, 10, vec![10, 30, 40]),
		(6, 10, vec![20, 30, 40]),
		(7, 10, vec![20, 30]),
		(8, 10, vec![10]),
		// self votes.
		(10, 10, vec![10]),
		(20, 20, vec![20]),
		(30, 30, vec![30]),
		(40, 40, vec![40]),
	];
	pub static LastIteratedVoterIndex: Option<usize> = None;

	pub static OnChianFallback: bool = true; // TODO: this should be false by default.
	pub static DesiredTargets: u32 = 2;
	pub static SignedPhase: u64 = 10;
	pub static UnsignedPhase: u64 = 5;
	pub static SignedMaxSubmissions: u32 = 5;
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositByte: Balance = 0;
	pub static SignedDepositWeight: Balance = 0;
	pub static SignedRewardBase: Balance = 7;
	pub static SignedMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxIterations: u32 = 5;
	pub static MinerTxPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = 256;
	pub static MockWeightInfo: bool = false;
	pub static VoterSnapshotPerBlock: VoterIndex = u32::max_value();

	pub static EpochLength: u64 = 30;
	pub static Pages: PageIndex = 1;
}

// Hopefully this won't be too much of a hassle to maintain.
pub struct DualMockWeightInfo;
impl multi_phase::weights::WeightInfo for DualMockWeightInfo {
	fn on_initialize_nothing() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::on_initialize_nothing()
		}
	}
	fn on_initialize_open_signed() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::on_initialize_open_signed()
		}
	}
	fn on_initialize_open_unsigned_with_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::on_initialize_open_unsigned_with_snapshot()
		}
	}
	fn on_initialize_open_unsigned_without_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::on_initialize_open_unsigned_without_snapshot()
		}
	}
	fn finalize_signed_phase_accept_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::finalize_signed_phase_accept_solution()
		}
	}
	fn finalize_signed_phase_reject_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::finalize_signed_phase_reject_solution()
		}
	}
	fn submit(c: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::submit(c)
		}
	}
	fn elect_queued(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::elect_queued(v, t, a, d)
		}
	}
	fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_phase::weights::WeightInfo>::submit_unsigned(v, t, a, d)
		}
	}
	fn feasibility_check(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_phase::weights::WeightInfo>::feasibility_check(v, t, a, d)
		}
	}
}

impl crate::verifier::Config for Runtime {
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
}

impl crate::unsigned::Config for Runtime {
	type OffchainRepeat = OffchainRepeat;
	type MinerMaxIterations = MinerMaxIterations;
	type MinerMaxWeight = MinerMaxWeight;
	type MinerMaxLength = MinerMaxLength;
	type MinerTxPriority = MinerTxPriority;
	type WeightInfo = ();
}

impl crate::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type EstimateCallFee = frame_support::traits::ConstU32<8>;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type SignedRewardBase = SignedRewardBase;
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SignedMaxWeight = SignedMaxWeight;
	type SignedMaxSubmissions = SignedMaxSubmissions;
	type SlashHandler = ();
	type RewardHandler = ();
	type DataProvider = MockStaking;
	type BenchmarkingConfig = ();
	type Fallback = MockFallback;
	type VoterSnapshotPerBlock = VoterSnapshotPerBlock;
	type Solution = TestNposSolution;
	type WeightInfo = DualMockWeightInfo;
	type Verifier = VerifierPallet;
	type Pages = Pages;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub struct OnChainConfig;
impl onchain::Config for OnChainConfig {
	type AccountId = AccountId;
	type BlockNumber = u64;
	type Accuracy = sp_runtime::Perbill;
	type DataProvider = MockStaking;
	type TargetsPageSize = ();
	type VoterPageSize = ();
}

pub struct MockFallback;
impl ElectionProvider<AccountId, u64> for MockFallback {
	type Error = ElectionError;
	type DataProvider = MockStaking;

	fn elect(remaining: PageIndex) -> Result<Supports<AccountId>, Self::Error> {
		if OnChianFallback::get() {
			onchain::OnChainSequentialPhragmen::<OnChainConfig>::elect(remaining)
				.map_err(Into::into)
		} else {
			InitiateEmergencyPhase::<Runtime>::elect(remaining)
		}
	}
}

pub struct MockStaking;
impl ElectionDataProvider<AccountId, u64> for MockStaking {
	const MAXIMUM_VOTES_PER_VOTER: u32 = <TestNposSolution as NposSolution>::LIMIT as u32;
	fn targets(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
	) -> data_provider::Result<Vec<AccountId>> {
		let targets = Targets::get();

		if remaining != 0 {
			return Err("targets shall not have more than a single page")
		}
		if maybe_max_len.map_or(false, |max_len| targets.len() > max_len) {
			return Err("Targets too big")
		}

		Ok(targets)
	}

	fn voters(
		maybe_max_len: Option<usize>,
		remaining: PageIndex,
	) -> data_provider::Result<Vec<(AccountId, VoteWeight, Vec<AccountId>)>> {
		let mut voters = Voters::get();

		// jump to the first non-iterated, if this is a follow up.
		if let Some(index) = LastIteratedVoterIndex::get() {
			voters = voters.iter().skip(index).cloned().collect::<Vec<_>>();
		}

		// take as many as you can.
		if let Some(max_len) = maybe_max_len {
			voters.truncate(max_len)
		}

		if voters.is_empty() {
			return Ok(vec![])
		}

		if remaining > 0 {
			let last = voters.last().cloned().unwrap();
			LastIteratedVoterIndex::set(Some(
				Voters::get().iter().position(|v| v == &last).map(|i| i + 1).unwrap(),
			));
		} else {
			LastIteratedVoterIndex::set(None)
		}

		Ok(voters)
	}
	fn desired_targets() -> data_provider::Result<u32> {
		Ok(DesiredTargets::get())
	}

	fn next_election_prediction(now: u64) -> u64 {
		now + EpochLength::get() - now % EpochLength::get()
	}

	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn put_snapshot(
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
		targets: Vec<AccountId>,
		_target_stake: Option<VoteWeight>,
	) {
		Targets::set(targets);
		Voters::set(voters);
	}

	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn clear() {
		Targets::set(vec![]);
		Voters::set(vec![]);
	}

	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_voter(voter: AccountId, weight: VoteWeight, targets: Vec<AccountId>) {
		let mut current = Voters::get();
		current.push((voter, weight, targets));
		Voters::set(current);
	}

	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn add_target(target: AccountId) {
		let mut current = Targets::get();
		current.push(target);
		Targets::set(current);

		// to be on-par with staking, we add a self vote as well. the stake is really not that
		// important.
		let mut current = Voters::get();
		current.push((target, ExistentialDeposit::get() as u64, vec![target]));
		Voters::set(current);
	}
}

#[derive(Default)]
pub struct ExtBuilder {}

impl ExtBuilder {
	pub fn miner_tx_priority(self, p: u64) -> Self {
		<MinerTxPriority>::set(p);
		self
	}
	pub fn solution_improvement_threshold(self, p: Perbill) -> Self {
		<SolutionImprovementThreshold>::set(p);
		self
	}
	pub fn phases(self, signed: u64, unsigned: u64) -> Self {
		<SignedPhase>::set(signed);
		<UnsignedPhase>::set(unsigned);
		self
	}
	pub fn pages(self, pages: PageIndex) -> Self {
		<Pages>::set(pages);
		self
	}
	pub fn voter_per_page(self, count: u32) -> Self {
		<VoterSnapshotPerBlock>::set(count);
		self
	}
	pub fn miner_weight(self, weight: Weight) -> Self {
		<MinerMaxWeight>::set(weight);
		self
	}
	pub fn mock_weight_info(self, mock: bool) -> Self {
		<MockWeightInfo>::set(mock);
		self
	}
	pub fn desired_targets(self, t: u32) -> Self {
		<DesiredTargets>::set(t);
		self
	}
	pub fn add_voter(self, who: AccountId, stake: Balance, targets: Vec<AccountId>) -> Self {
		VOTERS.with(|v| v.borrow_mut().push((who, stake, targets)));
		self
	}
	pub fn signed_max_submission(self, count: u32) -> Self {
		<SignedMaxSubmissions>::set(count);
		self
	}
	pub fn signed_deposit(self, base: u64, byte: u64, weight: u64) -> Self {
		<SignedDepositBase>::set(base);
		<SignedDepositByte>::set(byte);
		<SignedDepositWeight>::set(weight);
		self
	}
	pub fn signed_weight(self, weight: Weight) -> Self {
		<SignedMaxWeight>::set(weight);
		self
	}

	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![
				// bunch of account for submitting stuff only.
				(99, 100),
				(999, 100),
				(9999, 100),
			],
		}
		.assimilate_storage(&mut storage);

		sp_io::TestExternalities::from(storage)
	}

	pub fn build_offchainify(
		self,
		iters: u32,
	) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
		let mut ext = self.build();
		let (offchain, offchain_state) = TestOffchainExt::new();
		let (pool, pool_state) = TestTransactionPoolExt::new();

		let mut seed = [0_u8; 32];
		seed[0..4].copy_from_slice(&iters.to_le_bytes());
		offchain_state.write().seed = seed;

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		(ext, pool_state)
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}

pub(crate) fn balances(who: &u64) -> (u64, u64) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}

pub(crate) fn create_all_snapshots() {
	let _ = (0..Pages::get())
		.rev()
		.map(|p| MultiPhase::create_voters_snapshot_paged(p))
		.collect::<Result<Vec<_>, _>>()
		.unwrap();
	let _ = MultiPhase::create_targets_snapshot().unwrap();
}

pub(crate) fn witness() -> SolutionOrSnapshotSize {
	let voters = <PagedVoterSnapshot<Runtime>>::iter()
		.map(|(_, voters)| voters)
		.fold(0u32, |acc, next| acc.saturating_add(next.len() as u32));
	let targets = <PagedTargetSnapshot<Runtime>>::get(0)
		.map(|t| t.len() as u32)
		.unwrap_or_default();
	SolutionOrSnapshotSize { voters, targets }
}

// TODO: post-condition check that the metadata storage items are consistent: they must all
// exist at the same time.
pub(crate) fn ensure_snapshot(exists: bool, up_to_page: PageIndex) {
	assert!(up_to_page > 0);

	assert!(exists ^ !MultiPhase::desired_targets().is_some());
	assert!(exists ^ !MultiPhase::snapshot_metadata().is_some());
	assert!(exists ^ !<PagedTargetSnapshot<Runtime>>::contains_key(0));

	// TODO: snapshot is created from top to bottom..
	(Pages::get() - 1..=0).take(up_to_page.into()).for_each(|p| {
		assert!(
			exists ^ !<PagedVoterSnapshot<Runtime>>::contains_key(p),
			"voter page {} not {}",
			p,
			exists
		);
	});
}

#[test]
fn raw_paged_solution_works() {
	// TODO: do a 3 page version of this as well, helps a lot with understanding.
	ExtBuilder::default().pages(2).voter_per_page(4).build_and_execute(|| {
		create_all_snapshots();

		// 2 pages of 8 voters
		assert_eq!(<PagedVoterSnapshot<Runtime>>::iter().count(), 2);
		assert_eq!(<PagedVoterSnapshot<Runtime>>::iter().map(|(_p, x)| x).flatten().count(), 8);
		// 1 page of 4 voters
		assert_eq!(<PagedTargetSnapshot<Runtime>>::iter().count(), 1);
		assert_eq!(<PagedTargetSnapshot<Runtime>>::iter().map(|(_p, x)| x).flatten().count(), 4);

		let paged = raw_paged_solution();
		assert_eq!(
			paged.solution_pages,
			vec![
				// in page 0 of the snapshot.
				TestNposSolution {
					votes1: vec![(1, 3), (3, 0)],
					votes2: vec![(0, [(0, PerU16::from_parts(32768))], 3)],
					..Default::default()
				},
				// in page 1 of the snapshot.
				TestNposSolution {
					votes1: vec![(0, 0), (1, 3), (2, 3)],
					votes2: vec![(3, [(0, PerU16::from_parts(32768))], 3)],
					..Default::default()
				},
			]
		);

		// this solution must be feasible.
		let supports = paged
			.solution_pages
			.iter()
			.enumerate()
			.map(|(i, p)| {
				let page_index = i as PageIndex;
				VerifierPallet::feasibility_check_page(p.clone(), page_index).unwrap()
			})
			.collect::<Vec<_>>();

		assert_eq!(
			supports,
			vec![
				// page0, supports from voters 5, 6, 7, 8
				vec![
					(10, Support { total: 15, voters: vec![(8, 10), (5, 5)] }),
					(40, Support { total: 15, voters: vec![(6, 10), (5, 5)] })
				],
				// page1 supports from voters 1, 2, 3, 4
				vec![
					(10, Support { total: 15, voters: vec![(1, 10), (4, 5)] }),
					(40, Support { total: 25, voters: vec![(2, 10), (3, 10), (4, 5)] })
				]
			]
		);

		assert_eq!(paged.score, [30, 70, 2500]);
	})
}

#[test]
fn staking_mock_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(MockStaking::voters(None, 0).unwrap().len(), 12);
		assert!(LastIteratedVoterIndex::get().is_none());

		assert_eq!(
			MockStaking::voters(Some(4), 0)
				.unwrap()
				.into_iter()
				.map(|(x, _, _)| x)
				.collect::<Vec<_>>(),
			vec![1, 2, 3, 4],
		);
		assert!(LastIteratedVoterIndex::get().is_none());

		assert_eq!(
			MockStaking::voters(Some(4), 2)
				.unwrap()
				.into_iter()
				.map(|(x, _, _)| x)
				.collect::<Vec<_>>(),
			vec![1, 2, 3, 4],
		);
		assert_eq!(LastIteratedVoterIndex::get().unwrap(), 4);
		assert_eq!(
			MockStaking::voters(Some(4), 1)
				.unwrap()
				.into_iter()
				.map(|(x, _, _)| x)
				.collect::<Vec<_>>(),
			vec![5, 6, 7, 8],
		);
		assert_eq!(LastIteratedVoterIndex::get().unwrap(), 8);
		assert_eq!(
			MockStaking::voters(Some(4), 0)
				.unwrap()
				.into_iter()
				.map(|(x, _, _)| x)
				.collect::<Vec<_>>(),
			vec![10, 20, 30, 40],
		);
		assert!(LastIteratedVoterIndex::get().is_none());
	})
}
