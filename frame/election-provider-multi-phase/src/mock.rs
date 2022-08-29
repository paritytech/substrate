// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
use crate::{self as multi_phase, unsigned::MinerConfig};
use frame_election_provider_support::{
	data_provider,
	onchain::{self, UnboundedExecution},
	ElectionDataProvider, NposSolution, SequentialPhragmen,
};
pub use frame_support::{assert_noop, assert_ok, pallet_prelude::GetDefault};
use frame_support::{
	bounded_vec, parameter_types,
	traits::{ConstU32, Hooks},
	weights::Weight,
	BoundedVec,
};
use multi_phase::unsigned::{IndexAssignmentOf, VoterOf};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, seq_phragmen, to_supports, BalancingConfig,
	ElectionResult, EvaluateSupport,
};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16,
};
use std::sync::Arc;

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, Call, (), ()>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>, Config},
		Balances: pallet_balances::{Pallet, Call, Event<T>, Config<T>},
		MultiPhase: multi_phase::{Pallet, Call, Event<T>},
	}
);

pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

frame_election_provider_support::generate_solution_type!(
	#[compact]
	pub struct TestNposSolution::<
		VoterIndex = VoterIndex,
		TargetIndex = TargetIndex,
		Accuracy = PerU16,
		MaxVoters = ConstU32::<2_000>
	>(16)
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
pub fn roll_to(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiPhase::on_initialize(i);
	}
}

pub fn roll_to_with_ocw(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiPhase::on_initialize(i);
		MultiPhase::offchain_worker(i);
	}
}

pub struct TrimHelpers {
	pub voters: Vec<VoterOf<Runtime>>,
	pub assignments: Vec<IndexAssignmentOf<Runtime>>,
	pub encoded_size_of:
		Box<dyn Fn(&[IndexAssignmentOf<Runtime>]) -> Result<usize, sp_npos_elections::Error>>,
	pub voter_index: Box<
		dyn Fn(
			&<Runtime as frame_system::Config>::AccountId,
		) -> Option<SolutionVoterIndexOf<Runtime>>,
	>,
}

/// Helpers for setting up trimming tests.
///
/// Assignments are pre-sorted in reverse order of stake.
pub fn trim_helpers() -> TrimHelpers {
	let RoundSnapshot { voters, targets } = MultiPhase::snapshot().unwrap();
	let stakes: std::collections::HashMap<_, _> =
		voters.iter().map(|(id, stake, _)| (*id, *stake)).collect();

	// Compute the size of a solution comprised of the selected arguments.
	//
	// This function completes in `O(edges)`; it's expensive, but linear.
	let encoded_size_of = Box::new(|assignments: &[IndexAssignmentOf<Runtime>]| {
		SolutionOf::<Runtime>::try_from(assignments).map(|s| s.encoded_size())
	});
	let cache = helpers::generate_voter_cache::<Runtime>(&voters);
	let voter_index = helpers::voter_index_fn_owned::<Runtime>(cache);
	let target_index = helpers::target_index_fn::<Runtime>(&targets);

	let desired_targets = MultiPhase::desired_targets().unwrap();

	let ElectionResult::<_, SolutionAccuracyOf<Runtime>> { mut assignments, .. } =
		seq_phragmen(desired_targets as usize, targets.clone(), voters.clone(), None).unwrap();

	// sort by decreasing order of stake
	assignments.sort_unstable_by_key(|assignment| {
		std::cmp::Reverse(stakes.get(&assignment.who).cloned().unwrap_or_default())
	});

	// convert to IndexAssignment
	let assignments = assignments
		.iter()
		.map(|assignment| {
			IndexAssignmentOf::<Runtime>::new(assignment, &voter_index, &target_index)
		})
		.collect::<Result<Vec<_>, _>>()
		.expect("test assignments don't contain any voters with too many votes");

	TrimHelpers { voters, assignments, encoded_size_of, voter_index: Box::new(voter_index) }
}

/// Spit out a verifiable raw solution.
///
/// This is a good example of what an offchain miner would do.
pub fn raw_solution() -> RawSolution<SolutionOf<Runtime>> {
	let RoundSnapshot { voters, targets } = MultiPhase::snapshot().unwrap();
	let desired_targets = MultiPhase::desired_targets().unwrap();

	let ElectionResult::<_, SolutionAccuracyOf<Runtime>> { winners: _, assignments } =
		seq_phragmen(desired_targets as usize, targets.clone(), voters.clone(), None).unwrap();

	// closures
	let cache = helpers::generate_voter_cache::<Runtime>(&voters);
	let voter_index = helpers::voter_index_fn_linear::<Runtime>(&voters);
	let target_index = helpers::target_index_fn_linear::<Runtime>(&targets);
	let stake_of = helpers::stake_of_fn::<Runtime>(&voters, &cache);

	let score = {
		let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of).unwrap();
		to_supports(&staked).evaluate()
	};
	let solution =
		<SolutionOf<Runtime>>::from_assignment(&assignments, &voter_index, &target_index).unwrap();

	let round = MultiPhase::round();
	RawSolution { solution, score, round }
}

pub fn witness() -> SolutionOrSnapshotSize {
	MultiPhase::snapshot()
		.map(|snap| SolutionOrSnapshotSize {
			voters: snap.voters.len() as u32,
			targets: snap.targets.len() as u32,
		})
		.unwrap_or_default()
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = BlockNumber;
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
	type MaxConsumers = ConstU32<16>;
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

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum MockedWeightInfo {
	Basic,
	Complex,
	Real,
}

parameter_types! {
	pub static Targets: Vec<AccountId> = vec![10, 20, 30, 40];
	pub static Voters: Vec<VoterOf<Runtime>> = vec![
		(1, 10, bounded_vec![10, 20]),
		(2, 10, bounded_vec![30, 40]),
		(3, 10, bounded_vec![40]),
		(4, 10, bounded_vec![10, 20, 30, 40]),
		// self votes.
		(10, 10, bounded_vec![10]),
		(20, 20, bounded_vec![20]),
		(30, 30, bounded_vec![30]),
		(40, 40, bounded_vec![40]),
	];

	pub static DesiredTargets: u32 = 2;
	pub static SignedPhase: BlockNumber = 10;
	pub static UnsignedPhase: BlockNumber = 5;
	pub static SignedMaxSubmissions: u32 = 5;
	pub static SignedMaxRefunds: u32 = 1;
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositByte: Balance = 0;
	pub static SignedDepositWeight: Balance = 0;
	pub static SignedRewardBase: Balance = 7;
	pub static SignedMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerTxPriority: u64 = 100;
	pub static BetterSignedThreshold: Perbill = Perbill::zero();
	pub static BetterUnsignedThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = 256;
	pub static MockWeightInfo: MockedWeightInfo = MockedWeightInfo::Real;
	pub static MaxElectingVoters: VoterIndex = u32::max_value();
	pub static MaxElectableTargets: TargetIndex = TargetIndex::max_value();

	pub static EpochLength: u64 = 30;
	pub static OnChainFallback: bool = true;
}

pub struct OnChainSeqPhragmen;
impl onchain::Config for OnChainSeqPhragmen {
	type System = Runtime;
	type Solver = SequentialPhragmen<AccountId, SolutionAccuracyOf<Runtime>, Balancing>;
	type DataProvider = StakingMock;
	type WeightInfo = ();
}

pub struct MockFallback;
impl ElectionProvider for MockFallback {
	type AccountId = AccountId;
	type BlockNumber = u64;
	type Error = &'static str;
	type DataProvider = StakingMock;

	fn elect() -> Result<Supports<AccountId>, Self::Error> {
		Self::elect_with_bounds(Bounded::max_value(), Bounded::max_value())
	}
}

impl InstantElectionProvider for MockFallback {
	fn elect_with_bounds(
		max_voters: usize,
		max_targets: usize,
	) -> Result<Supports<Self::AccountId>, Self::Error> {
		if OnChainFallback::get() {
			onchain::UnboundedExecution::<OnChainSeqPhragmen>::elect_with_bounds(
				max_voters,
				max_targets,
			)
			.map_err(|_| "onchain::UnboundedExecution failed.")
		} else {
			super::NoFallback::<Runtime>::elect_with_bounds(max_voters, max_targets)
		}
	}
}

parameter_types! {
	pub static Balancing: Option<BalancingConfig> = Some( BalancingConfig { iterations: 0, tolerance: 0 } );
}

pub struct TestBenchmarkingConfig;
impl BenchmarkingConfig for TestBenchmarkingConfig {
	const VOTERS: [u32; 2] = [400, 600];
	const ACTIVE_VOTERS: [u32; 2] = [100, 300];
	const TARGETS: [u32; 2] = [200, 400];
	const DESIRED_TARGETS: [u32; 2] = [100, 180];

	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 1000;
	const MINER_MAXIMUM_VOTERS: u32 = 1000;

	const MAXIMUM_TARGETS: u32 = 200;
}

impl MinerConfig for Runtime {
	type AccountId = AccountId;
	type MaxLength = MinerMaxLength;
	type MaxWeight = MinerMaxWeight;
	type MaxVotesPerVoter = <StakingMock as ElectionDataProvider>::MaxVotesPerVoter;
	type Solution = TestNposSolution;

	fn solution_weight(v: u32, t: u32, a: u32, d: u32) -> Weight {
		match MockWeightInfo::get() {
			MockedWeightInfo::Basic => Weight::from_ref_time(
				(10 as u64).saturating_add((5 as u64).saturating_mul(a as u64)),
			),
			MockedWeightInfo::Complex =>
				Weight::from_ref_time((0 * v + 0 * t + 1000 * a + 0 * d) as u64),
			MockedWeightInfo::Real =>
				<() as multi_phase::weights::WeightInfo>::feasibility_check(v, t, a, d),
		}
	}
}

impl crate::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type EstimateCallFee = frame_support::traits::ConstU32<8>;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type BetterUnsignedThreshold = BetterUnsignedThreshold;
	type BetterSignedThreshold = BetterSignedThreshold;
	type OffchainRepeat = OffchainRepeat;
	type MinerTxPriority = MinerTxPriority;
	type SignedRewardBase = SignedRewardBase;
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SignedMaxWeight = SignedMaxWeight;
	type SignedMaxSubmissions = SignedMaxSubmissions;
	type SignedMaxRefunds = SignedMaxRefunds;
	type SlashHandler = ();
	type RewardHandler = ();
	type DataProvider = StakingMock;
	type WeightInfo = ();
	type BenchmarkingConfig = TestBenchmarkingConfig;
	type Fallback = MockFallback;
	type GovernanceFallback = UnboundedExecution<OnChainSeqPhragmen>;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type MaxElectingVoters = MaxElectingVoters;
	type MaxElectableTargets = MaxElectableTargets;
	type MinerConfig = Self;
	type Solver = SequentialPhragmen<AccountId, SolutionAccuracyOf<Runtime>, Balancing>;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

parameter_types! {
	pub MaxNominations: u32 = <TestNposSolution as NposSolution>::LIMIT as u32;
}

#[derive(Default)]
pub struct ExtBuilder {}

pub struct StakingMock;
impl ElectionDataProvider for StakingMock {
	type AccountId = AccountId;
	type BlockNumber = u64;
	type MaxVotesPerVoter = MaxNominations;

	fn electable_targets(maybe_max_len: Option<usize>) -> data_provider::Result<Vec<AccountId>> {
		let targets = Targets::get();

		if maybe_max_len.map_or(false, |max_len| targets.len() > max_len) {
			return Err("Targets too big")
		}

		Ok(targets)
	}

	fn electing_voters(
		maybe_max_len: Option<usize>,
	) -> data_provider::Result<Vec<VoterOf<Runtime>>> {
		let mut voters = Voters::get();
		if let Some(max_len) = maybe_max_len {
			voters.truncate(max_len)
		}

		Ok(voters)
	}

	fn desired_targets() -> data_provider::Result<u32> {
		Ok(DesiredTargets::get())
	}

	fn next_election_prediction(now: u64) -> u64 {
		now + EpochLength::get() - now % EpochLength::get()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn put_snapshot(
		voters: Vec<VoterOf<Runtime>>,
		targets: Vec<AccountId>,
		_target_stake: Option<VoteWeight>,
	) {
		Targets::set(targets);
		Voters::set(voters);
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn clear() {
		Targets::set(vec![]);
		Voters::set(vec![]);
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_voter(
		voter: AccountId,
		weight: VoteWeight,
		targets: frame_support::BoundedVec<AccountId, Self::MaxVotesPerVoter>,
	) {
		let mut current = Voters::get();
		current.push((voter, weight, targets));
		Voters::set(current);
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_target(target: AccountId) {
		let mut current = Targets::get();
		current.push(target);
		Targets::set(current);

		// to be on-par with staking, we add a self vote as well. the stake is really not that
		// important.
		let mut current = Voters::get();
		current.push((target, ExistentialDeposit::get() as u64, bounded_vec![target]));
		Voters::set(current);
	}
}

impl ExtBuilder {
	pub fn miner_tx_priority(self, p: u64) -> Self {
		<MinerTxPriority>::set(p);
		self
	}
	pub fn better_signed_threshold(self, p: Perbill) -> Self {
		<BetterSignedThreshold>::set(p);
		self
	}
	pub fn better_unsigned_threshold(self, p: Perbill) -> Self {
		<BetterUnsignedThreshold>::set(p);
		self
	}
	pub fn phases(self, signed: BlockNumber, unsigned: BlockNumber) -> Self {
		<SignedPhase>::set(signed);
		<UnsignedPhase>::set(unsigned);
		self
	}
	pub fn onchain_fallback(self, onchain: bool) -> Self {
		<OnChainFallback>::set(onchain);
		self
	}
	pub fn miner_weight(self, weight: Weight) -> Self {
		<MinerMaxWeight>::set(weight);
		self
	}
	pub fn mock_weight_info(self, mock: MockedWeightInfo) -> Self {
		<MockWeightInfo>::set(mock);
		self
	}
	pub fn desired_targets(self, t: u32) -> Self {
		<DesiredTargets>::set(t);
		self
	}
	pub fn add_voter(
		self,
		who: AccountId,
		stake: Balance,
		targets: BoundedVec<AccountId, MaxNominations>,
	) -> Self {
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

pub(crate) fn balances(who: &AccountId) -> (Balance, Balance) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}
