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
use crate::{self as multi_block, unsigned as unsigned_pallet, verifier as verifier_pallet};
use frame_election_provider_support::{
	data_provider, ElectionDataProvider, ExtendedBalance, Support,
};
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{parameter_types, traits::Hooks, weights::Weight};
use parking_lot::RwLock;
use sp_core::{
	crypto::UncheckedInto,
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
use std::{convert::TryFrom, sync::Arc, vec};
use substrate_test_utils::assert_eq_uvec;

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
		MultiBlock: multi_block::{Pallet, Event<T>},
		VerifierPallet: verifier_pallet::{Pallet},
		UnsignedPallet: unsigned_pallet::{Pallet, Call, ValidateUnsigned},
	}
);

pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type VoterIndex = u32;
pub(crate) type TargetIndex = u16;

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestNposSolution::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

/// All events of this pallet.
pub(crate) fn multi_block_events() -> Vec<super::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::MultiBlock(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

pub fn roll_to(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiBlock::on_initialize(i);
		VerifierPallet::on_initialize(i);
		UnsignedPallet::on_initialize(i);
	}
}

pub fn roll_to_snapshot_created() {
	let mut now = System::block_number() + 1;
	while !matches!(MultiBlock::current_phase(), Phase::Snapshot(0)) {
		System::set_block_number(now);
		MultiBlock::on_initialize(now);
		VerifierPallet::on_initialize(now);
		UnsignedPallet::on_initialize(now);
		now += 1;
	}
}

pub fn roll_to_with_ocw(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		MultiBlock::on_initialize(i);
		VerifierPallet::on_initialize(i);
		UnsignedPallet::on_initialize(i);

		MultiBlock::offchain_worker(i);
		VerifierPallet::offchain_worker(i);
		UnsignedPallet::offchain_worker(i);
	}
}

/// Creates a nested vec where the index of the first vec is the same as the key of the snapshot.
fn nested_voter_snapshot() -> Vec<Vec<Voter<Runtime>>> {
	let mut flatten: Vec<Vec<Voter<Runtime>>> = Vec::with_capacity(Pages::get() as usize);
	flatten.resize(Pages::get() as usize, vec![]);
	let voter_snapshot = crate::Snapshot::<Runtime>::voters_iter().collect::<Vec<_>>();
	for (page, voters) in voter_snapshot {
		flatten[page as usize] = voters
	}

	flatten
}

/// A fake solution that might pass the pre dispatch checks of the unsigned phase.
pub(crate) fn fake_unsigned_solution(score: ElectionScore) -> PagedRawSolution<Runtime> {
	let mut solution_pages: FixedVec<Option<SolutionOf<Runtime>>, Pages> = Default::default();
	*solution_pages.as_mut().last_mut().unwrap() = Some(Default::default());
	PagedRawSolution { score, solution_pages, ..Default::default() }
}

pub(crate) fn raw_paged_solution_low_score() -> PagedRawSolution<Runtime> {
	PagedRawSolution {
		solution_pages: FixedVec::<Option<SolutionOf<Runtime>>, Pages>::try_from(vec![
			None,
			None,
			Some(TestNposSolution {
				// 2 desired targets, both voting for themselves
				votes1: vec![(0, 0), (1, 2)],
				..Default::default()
			}),
		])
		.unwrap(),
		round: 1,
		score: [
			10,  // lowest staked
			20,  // total staked
			200, // sum of stakes squared
		],
	}
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
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
parameter_types! {
	pub const ExistentialDeposit: Balance = 1;
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
	pub static SignedPhase: BlockNumber = 10;
	pub static UnsignedPhase: BlockNumber = 5;
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

	pub static EpochLength: u64 = 30;
	// by default we stick to 3 pages to host our 12 voters.
	pub static VoterSnapshotPerBlock: VoterIndex = 4;
	pub static Pages: PageIndex = 3;
}

pub struct DualMockWeightInfo;
impl multi_block::weights::WeightInfo for DualMockWeightInfo {
	fn on_initialize_nothing() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_nothing()
		}
	}
	fn on_initialize_open_signed() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_signed()
		}
	}
	fn on_initialize_open_unsigned_with_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_unsigned_with_snapshot()
		}
	}
	fn on_initialize_open_unsigned_without_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_unsigned_without_snapshot()
		}
	}
	fn finalize_signed_phase_accept_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::finalize_signed_phase_accept_solution()
		}
	}
	fn finalize_signed_phase_reject_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::finalize_signed_phase_reject_solution()
		}
	}
	fn submit(c: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::submit(c)
		}
	}
	fn elect_queued(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::elect_queued(v, t, a, d)
		}
	}
	fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_block::weights::WeightInfo>::submit_unsigned(v, t, a, d)
		}
	}
	fn feasibility_check(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_block::weights::WeightInfo>::feasibility_check(v, t, a, d)
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
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
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
	type Error = &'static str;
	type DataProvider = MockStaking;

	fn elect(remaining: PageIndex) -> Result<Supports<AccountId>, Self::Error> {
		if OnChianFallback::get() {
			onchain::OnChainSequentialPhragmen::<OnChainConfig>::elect(remaining)
				.map_err(|_| "OnChainSequentialPhragmen failed")
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

	pub fn build_unchecked(self) -> sp_io::TestExternalities {
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

	/// Warning: this does not execute the post-sanity-checks.
	pub fn build_offchainify(
		self,
		iters: u32,
	) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
		let mut ext = self.build_unchecked();
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

	/// Build the externalities, and execute the given  s`test` closure with it.
	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		let mut ext = self.build_unchecked();
		ext.execute_with(test);
		ext.execute_with(sanity_checks);
	}
}

pub(crate) fn balances(who: &u64) -> (u64, u64) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}

pub(crate) fn witness() -> SolutionOrSnapshotSize {
	let voters = Snapshot::<Runtime>::voters_iter_flattened().count() as u32;
	let targets = Snapshot::<Runtime>::targets().map(|t| t.len() as u32).unwrap_or_default();
	SolutionOrSnapshotSize { voters, targets }
}

fn sanity_checks() {
	// TODO: check phase, and match snapshot to it.
	let _ = VerifierPallet::sanity_check().unwrap();
	let _ = UnsignedPallet::sanity_check().unwrap();
	let _ = MultiBlock::sanity_check().unwrap();
}

pub(crate) fn ensure_full_snapshot() {
	Snapshot::<Runtime>::assert_snapshot(true, Pages::get())
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
