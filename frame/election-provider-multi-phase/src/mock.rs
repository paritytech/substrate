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
use crate as multi_phase;
use multi_phase::unsigned::{IndexAssignmentOf, Voter};
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{
	parameter_types,
	traits::{Hooks},
	weights::Weight,
};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};
use frame_election_provider_support::{ElectionDataProvider, data_provider};
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, seq_phragmen, to_supports, to_without_backing,
	CompactSolution, ElectionResult, EvaluateSupport,
};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16,
};
use std::{convert::TryFrom, sync::Arc};

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
pub(crate) type BlockNumber = u32;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestCompact::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

/// All events of this pallet.
pub(crate) fn multi_phase_events() -> Vec<super::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::multi_phase(inner) = e { Some(inner) } else { None })
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

pub struct TrimHelpers {
	pub voters: Vec<Voter<Runtime>>,
	pub assignments: Vec<IndexAssignmentOf<Runtime>>,
	pub encoded_size_of:
		Box<dyn Fn(&[IndexAssignmentOf<Runtime>]) -> Result<usize, sp_npos_elections::Error>>,
	pub voter_index: Box<
		dyn Fn(
			&<Runtime as frame_system::Config>::AccountId,
		) -> Option<CompactVoterIndexOf<Runtime>>,
	>,
}

/// Helpers for setting up trimming tests.
///
/// Assignments are pre-sorted in reverse order of stake.
pub fn trim_helpers() -> TrimHelpers {
	let RoundSnapshot { voters, targets } = MultiPhase::snapshot().unwrap();
	let stakes: std::collections::HashMap<_, _> =
		voters.iter().map(|(id, stake, _)| (*id, *stake)).collect();

	// Compute the size of a compact solution comprised of the selected arguments.
	//
	// This function completes in `O(edges)`; it's expensive, but linear.
	let encoded_size_of = Box::new(|assignments: &[IndexAssignmentOf<Runtime>]| {
		CompactOf::<Runtime>::try_from(assignments).map(|compact| compact.encoded_size())
	});
	let cache = helpers::generate_voter_cache::<Runtime>(&voters);
	let voter_index = helpers::voter_index_fn_owned::<Runtime>(cache);
	let target_index = helpers::target_index_fn::<Runtime>(&targets);

	let desired_targets = MultiPhase::desired_targets().unwrap();

	let ElectionResult { mut assignments, .. } = seq_phragmen::<_, CompactAccuracyOf<Runtime>>(
		desired_targets as usize,
		targets.clone(),
		voters.clone(),
		None,
	)
	.unwrap();

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
pub fn raw_solution() -> RawSolution<CompactOf<Runtime>> {
	let RoundSnapshot { voters, targets } = MultiPhase::snapshot().unwrap();
	let desired_targets = MultiPhase::desired_targets().unwrap();

	let ElectionResult { winners, assignments } = seq_phragmen::<_, CompactAccuracyOf<Runtime>>(
		desired_targets as usize,
		targets.clone(),
		voters.clone(),
		None,
	)
	.unwrap();

	// closures
	let cache = helpers::generate_voter_cache::<Runtime>(&voters);
	let voter_index = helpers::voter_index_fn_linear::<Runtime>(&voters);
	let target_index = helpers::target_index_fn_linear::<Runtime>(&targets);
	let stake_of = helpers::stake_of_fn::<Runtime>(&voters, &cache);

	let winners = to_without_backing(winners);

	let score = {
		let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of).unwrap();
		to_supports(&winners, &staked).unwrap().evaluate()
	};
	let compact =
		<CompactOf<Runtime>>::from_assignment(&assignments, &voter_index, &target_index).unwrap();

	let round = MultiPhase::round();
	RawSolution { compact, score, round }
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
	type BaseCallFilter = ();
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
	type WeightInfo = ();
}

parameter_types! {
	pub static Targets: Vec<AccountId> = vec![10, 20, 30, 40];
	pub static Voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)> = vec![
		(1, 10, vec![10, 20]),
		(2, 10, vec![30, 40]),
		(3, 10, vec![40]),
		(4, 10, vec![10, 20, 30, 40]),
		// self votes.
		(10, 10, vec![10]),
		(20, 20, vec![20]),
		(30, 30, vec![30]),
		(40, 40, vec![40]),
	];

	pub static Fallback: FallbackStrategy = FallbackStrategy::OnChain;
	pub static DesiredTargets: u32 = 2;
	pub static SignedPhase: u64 = 10;
	pub static UnsignedPhase: u64 = 5;
	pub static MaxSignedSubmissions: u32 = 5;

	pub static MinerMaxIterations: u32 = 5;
	pub static MinerTxPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = 256;
	pub static MockWeightInfo: bool = false;

	pub static EpochLength: u64 = 30;
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
	fn elect_queued() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_phase::weights::WeightInfo>::elect_queued()
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

impl crate::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type OffchainRepeat = OffchainRepeat;
	type MinerMaxIterations = MinerMaxIterations;
	type MinerMaxWeight = MinerMaxWeight;
	type MinerMaxLength = MinerMaxLength;
	type MinerTxPriority = MinerTxPriority;
	type DataProvider = StakingMock;
	type WeightInfo = DualMockWeightInfo;
	type BenchmarkingConfig = ();
	type OnChainAccuracy = Perbill;
	type Fallback = Fallback;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type CompactSolution = TestCompact;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

#[derive(Default)]
pub struct ExtBuilder {}

pub struct StakingMock;
impl ElectionDataProvider<AccountId, u64> for StakingMock {
	const MAXIMUM_VOTES_PER_VOTER: u32 = <TestCompact as CompactSolution>::LIMIT as u32;
	fn targets(maybe_max_len: Option<usize>) -> data_provider::Result<(Vec<AccountId>, Weight)> {
		let targets = Targets::get();

		if maybe_max_len.map_or(false, |max_len| targets.len() > max_len) {
			return Err("Targets too big");
		}

		Ok((targets, 0))
	}

	fn voters(
		maybe_max_len: Option<usize>,
	) -> data_provider::Result<(Vec<(AccountId, VoteWeight, Vec<AccountId>)>, Weight)> {
		let voters = Voters::get();
		if maybe_max_len.map_or(false, |max_len| voters.len() > max_len) {
			return Err("Voters too big");
		}

		Ok((voters, 0))
	}
	fn desired_targets() -> data_provider::Result<(u32, Weight)> {
		Ok((DesiredTargets::get(), 0))
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
}

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
	pub fn fallback(self, fallback: FallbackStrategy) -> Self {
		<Fallback>::set(fallback);
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
