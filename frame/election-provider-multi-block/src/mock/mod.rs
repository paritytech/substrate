// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

mod signed;
mod staking;
mod weight_info;
use frame_system::EnsureRoot;
pub use signed::*;
pub use staking::*;

use super::*;
use crate::{
	self as multi_block,
	signed::{self as signed_pallet},
	unsigned::{
		self as unsigned_pallet,
		miner::{BaseMiner, MinerError},
	},
	verifier::{self as verifier_pallet, AsynchronousVerifier, Status},
};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_election_provider_support::NposSolution;
pub use frame_support::{assert_noop, assert_ok};
use frame_support::{bounded_vec, parameter_types, traits::Hooks, weights::Weight};
use parking_lot::RwLock;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	H256,
};
use sp_npos_elections::EvaluateSupport;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16, Perbill,
};
use std::{sync::Arc, vec};

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<AccountId, Call, (), ()>;

pub type Balance = u64;
pub type AccountId = u64;
pub type BlockNumber = u64;
pub type VoterIndex = u32;
pub type TargetIndex = u16;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>, Config},
		Balances: pallet_balances::{Pallet, Call, Event<T>, Config<T>},
		MultiBlock: multi_block::{Pallet, Event<T>},
		SignedPallet: signed_pallet::{Pallet, Event<T>},
		VerifierPallet: verifier_pallet::{Pallet, Event<T>},
		UnsignedPallet: unsigned_pallet::{Pallet, Call, ValidateUnsigned},
	}
);

frame_election_provider_support::generate_solution_type!(
	pub struct TestNposSolution::<VoterIndex = VoterIndex, TargetIndex = TargetIndex, Accuracy = PerU16>(16)
);

impl codec::MaxEncodedLen for TestNposSolution {
	fn max_encoded_len() -> usize {
		// TODO: https://github.com/paritytech/substrate/issues/10866
		unimplemented!();
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
	type MaxConsumers = ConstU32<16>;
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
	pub static Pages: PageIndex = 3;
	pub static UnsignedPhase: BlockNumber = 5;
	pub static SignedPhase: BlockNumber = 5;
	pub static SignedValidationPhase: BlockNumber = 5;

	pub static OnChianFallback: bool = false;
	pub static MinerTxPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static OffchainRepeat: BlockNumber = 5;
	pub static MinerMaxWeight: Weight = BlockWeights::get().max_block;
	pub static MinerMaxLength: u32 = 256;
	pub static MaxVotesPerVoter: u32 = <TestNposSolution as NposSolution>::LIMIT as u32;

	// by default we stick to 3 pages to host our 12 voters.
	pub static VoterSnapshotPerBlock: VoterIndex = 4;
	pub static TargetSnapshotPerBlock: TargetIndex = 8;
	pub static Lookahead: BlockNumber = 0;

	// we have 12 voters in the default setting, this should be enough to make sure they are not
	// trimmed accidentally in any test.
	#[derive(Encode, Decode, PartialEq, Eq, Debug, scale_info::TypeInfo, MaxEncodedLen)] // TODO: should be removed
	pub static MaxBackersPerWinner: u32 = 12;
	// we have 4 targets in total and we desire `Desired` thereof, no single page can represent more
	// than the min of these two.
	#[derive(Encode, Decode, PartialEq, Eq, Debug, scale_info::TypeInfo, MaxEncodedLen)]
	pub static MaxWinnersPerPage: u32 = (staking::Targets::get().len() as u32).min(staking::DesiredTargets::get());
}

impl crate::verifier::Config for Runtime {
	type Event = Event;
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type MaxBackersPerWinner = MaxBackersPerWinner;
	type MaxWinnersPerPage = MaxWinnersPerPage;
	type SolutionDataProvider = signed::DualSignedPhase;
	type WeightInfo = ();
}

pub struct MockUnsignedWeightInfo;
impl crate::unsigned::WeightInfo for MockUnsignedWeightInfo {
	fn submit_unsigned(_v: u32, _t: u32, a: u32, _d: u32) -> Weight {
		a as Weight
	}
}

impl crate::unsigned::Config for Runtime {
	type OffchainRepeat = OffchainRepeat;
	type MinerMaxWeight = MinerMaxWeight;
	type MinerMaxLength = MinerMaxLength;
	type MinerTxPriority = MinerTxPriority;
	type OffchainSolver =
		frame_election_provider_support::SequentialPhragmen<Self::AccountId, Perbill>;
	type WeightInfo = MockUnsignedWeightInfo;
}

impl crate::Config for Runtime {
	type Event = Event;
	type SignedPhase = SignedPhase;
	type SignedValidationPhase = SignedValidationPhase;
	type UnsignedPhase = UnsignedPhase;
	type DataProvider = staking::MockStaking;
	type Fallback = MockFallback;
	type TargetSnapshotPerBlock = TargetSnapshotPerBlock;
	type VoterSnapshotPerBlock = VoterSnapshotPerBlock;
	type Lookahead = Lookahead;
	type Solution = TestNposSolution;
	type WeightInfo = weight_info::DualMockWeightInfo;
	type Verifier = VerifierPallet;
	type AdminOrigin = EnsureRoot<AccountId>;
	type Pages = Pages;
}

impl onchain::Config for Runtime {
	type Accuracy = sp_runtime::Perbill;
	type DataProvider = staking::MockStaking;
	type TargetPageSize = ();
	type VoterPageSize = ();
	type MaxBackersPerWinner = MaxBackersPerWinner;
	type MaxWinnersPerPage = MaxWinnersPerPage;
}

pub struct MockFallback;
impl ElectionProvider for MockFallback {
	type AccountId = AccountId;
	type BlockNumber = u64;
	type Error = &'static str;
	type DataProvider = staking::MockStaking;
	type Pages = ConstU32<1>;
	type MaxBackersPerWinner = MaxBackersPerWinner;
	type MaxWinnersPerPage = MaxWinnersPerPage;

	fn elect(remaining: PageIndex) -> Result<BoundedSupportsOf<Self>, Self::Error> {
		if OnChianFallback::get() {
			onchain::OnChainSequentialPhragmen::<Runtime>::elect(remaining)
				.map_err(|_| "OnChainSequentialPhragmen failed")
		} else {
			// NOTE: this pesky little trick here is to avoid a clash of type, since `Ok` of our
			// election provider and our fallback is not the same
			let err = InitiateEmergencyPhase::<Runtime>::elect(remaining).unwrap_err();
			Err(err)
		}
	}
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub struct ExtBuilder {}

impl ExtBuilder {
	pub fn full() -> Self {
		Self {}
	}

	pub fn verifier() -> Self {
		SignedPhase::set(0);
		SignedValidationPhase::set(0);
		signed::SignedPhaseSwitch::set(signed::SignedSwitch::Mock);
		Self {}
	}

	pub fn unsigned() -> Self {
		SignedPhase::set(0);
		SignedValidationPhase::set(0);
		signed::SignedPhaseSwitch::set(signed::SignedSwitch::Mock);
		Self {}
	}

	pub fn signed() -> Self {
		UnsignedPhase::set(0);
		Self {}
	}
}

impl ExtBuilder {
	pub(crate) fn max_backing_per_target(self, c: u32) -> Self {
		MaxBackersPerWinner::set(c);
		self
	}
	pub(crate) fn miner_tx_priority(self, p: u64) -> Self {
		MinerTxPriority::set(p);
		self
	}
	pub(crate) fn solution_improvement_threshold(self, p: Perbill) -> Self {
		SolutionImprovementThreshold::set(p);
		self
	}
	pub(crate) fn pages(self, pages: PageIndex) -> Self {
		Pages::set(pages);
		self
	}
	pub(crate) fn lookahead(self, lookahead: BlockNumber) -> Self {
		Lookahead::set(lookahead);
		self
	}
	pub(crate) fn voter_per_page(self, count: u32) -> Self {
		VoterSnapshotPerBlock::set(count);
		self
	}
	pub(crate) fn miner_weight(self, weight: Weight) -> Self {
		MinerMaxWeight::set(weight);
		self
	}
	pub(crate) fn miner_max_length(self, len: u32) -> Self {
		MinerMaxLength::set(len);
		self
	}
	pub(crate) fn desired_targets(self, t: u32) -> Self {
		staking::DesiredTargets::set(t);
		self
	}
	pub(crate) fn signed_phase(self, d: BlockNumber, v: BlockNumber) -> Self {
		SignedPhase::set(d);
		SignedValidationPhase::set(v);
		self
	}
	pub(crate) fn unsigned_phase(self, d: BlockNumber) -> Self {
		UnsignedPhase::set(d);
		self
	}
	pub(crate) fn signed_validation_phase(self, d: BlockNumber) -> Self {
		SignedValidationPhase::set(d);
		self
	}
	pub(crate) fn add_voter(self, who: AccountId, stake: Balance, targets: Vec<AccountId>) -> Self {
		staking::VOTERS.with(|v| v.borrow_mut().push((who, stake, targets.try_into().unwrap())));
		self
	}
	pub(crate) fn onchain_fallback(self, enable: bool) -> Self {
		OnChianFallback::set(enable);
		self
	}
	pub(crate) fn build_unchecked(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![
				// bunch of account for submitting stuff only.
				(91, 100),
				(92, 100),
				(93, 100),
				(94, 100),
				(95, 100),
				(96, 100),
				(97, 100),
				(99, 100),
				(999, 100),
				(9999, 100),
			],
		}
		.assimilate_storage(&mut storage);

		sp_io::TestExternalities::from(storage)
	}

	/// Warning: this does not execute the post-sanity-checks.
	pub(crate) fn build_offchainify(self) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
		let mut ext = self.build_unchecked();
		let (offchain, _offchain_state) = TestOffchainExt::new();
		let (pool, pool_state) = TestTransactionPoolExt::new();

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		(ext, pool_state)
	}

	/// Build the externalities, and execute the given  s`test` closure with it.
	pub(crate) fn build_and_execute(self, test: impl FnOnce() -> ()) {
		let mut ext = self.build_unchecked();
		ext.execute_with_sanity_checks(test);
	}
}

pub trait ExecuteWithSanityChecks {
	fn execute_with_sanity_checks(&mut self, test: impl FnOnce() -> ());
}

impl ExecuteWithSanityChecks for sp_io::TestExternalities {
	fn execute_with_sanity_checks(&mut self, test: impl FnOnce() -> ()) {
		self.execute_with(test);
		self.execute_with(all_pallets_sanity_checks)
	}
}

fn all_pallets_sanity_checks() {
	let _ = VerifierPallet::sanity_check()
		.and(UnsignedPallet::sanity_check())
		.and(MultiBlock::sanity_check())
		.and(SignedPallet::sanity_check())
		.unwrap();
}

/// Fully verify a solution.
///
/// This will progress the blocks until the verifier pallet is done verifying it.
///
/// The solution must have already been loaded via `load_and_start_verification`.
///
/// Return the final supports, which is the outcome. If this succeeds, then the valid variant of the
/// `QueuedSolution` form `verifier` is ready to be read.
pub fn roll_to_full_verification() -> Vec<BoundedSupportsOf<MultiBlock>> {
	// we must be ready to verify.
	assert_eq!(VerifierPallet::status(), Status::Ongoing(Pages::get() - 1));

	while matches!(VerifierPallet::status(), Status::Ongoing(_)) {
		roll_to(System::block_number() + 1);
	}

	(MultiBlock::lsp()..=MultiBlock::msp())
		.map(|p| VerifierPallet::get_queued_solution_page(p).unwrap_or_default())
		.collect::<Vec<_>>()
}

/// Generate a single page of `TestNposSolution` from the give supports.
///
/// All of the voters in this support must live in a single page of the snapshot, noted by
/// `snapshot_page`.
pub fn solution_from_supports(
	supports: sp_npos_elections::Supports<AccountId>,
	snapshot_page: PageIndex,
) -> TestNposSolution {
	let staked = sp_npos_elections::supports_to_staked_assignment(supports);
	let assignments = sp_npos_elections::assignment_staked_to_ratio_normalized(staked).unwrap();

	let voters = crate::Snapshot::<Runtime>::voters(snapshot_page).unwrap();
	let targets = crate::Snapshot::<Runtime>::targets().unwrap();
	let voter_index = helpers::voter_index_fn_linear::<Runtime>(&voters);
	let target_index = helpers::target_index_fn_linear::<Runtime>(&targets);

	TestNposSolution::from_assignment(&assignments, &voter_index, &target_index).unwrap()
}

/// Generate a raw paged solution from the given vector of supports.
///
/// Given vector must be aligned with the snapshot, at most need to be 'pagified' which we do
/// internally.
pub fn raw_paged_from_supports(
	paged_supports: Vec<sp_npos_elections::Supports<AccountId>>,
	round: u32,
) -> PagedRawSolution<Runtime> {
	let score = {
		let flattened = paged_supports.iter().cloned().flatten().collect::<Vec<_>>();
		flattened.evaluate()
	};

	let solution_pages = paged_supports
		.pagify(Pages::get())
		.map(|(page_index, page_support)| solution_from_supports(page_support.to_vec(), page_index))
		.collect::<Vec<_>>();

	let solution_pages = solution_pages.try_into().unwrap();
	PagedRawSolution { solution_pages, score, round }
}

/// ensure that the snapshot fully exists.
///
/// NOTE: this should not be used that often, because we check snapshot in sanity checks, which are
/// called ALL THE TIME.
pub fn assert_full_snapshot() {
	assert_ok!(Snapshot::<Runtime>::ensure_snapshot(true, Pages::get()));
}

/// ensure that the no snapshot exists.
///
/// NOTE: this should not be used that often, because we check snapshot in sanity checks, which are
/// called ALL THE TIME.
pub fn assert_none_snapshot() {
	assert_ok!(Snapshot::<Runtime>::ensure_snapshot(false, Pages::get()));
}

/// Simple wrapper for mining a new solution. Just more handy in case the interface of mine solution
/// changes.
///
/// For testing, we never want to do reduce.
pub fn mine_full_solution() -> Result<PagedRawSolution<Runtime>, MinerError<Runtime>> {
	BaseMiner::<Runtime>::mine_solution(Pages::get(), false)
}

/// Same as [`mine_full_solution`] but with custom pages.
pub fn mine_solution(pages: PageIndex) -> Result<PagedRawSolution<Runtime>, MinerError<Runtime>> {
	BaseMiner::<Runtime>::mine_solution(pages, false)
}

/// Assert that `count` voters exist across `pages` number of pages.
pub fn ensure_voters(pages: PageIndex, count: usize) {
	assert_eq!(crate::Snapshot::<Runtime>::voter_pages(), pages);
	assert_eq!(crate::Snapshot::<Runtime>::voters_iter_flattened().count(), count);
}

/// Assert that `count` targets exist across `pages` number of pages.
pub fn ensure_targets(pages: PageIndex, count: usize) {
	assert_eq!(crate::Snapshot::<Runtime>::target_pages(), pages);
	assert_eq!(crate::Snapshot::<Runtime>::targets().unwrap().len(), count);
}

/// get the events of the multi-block pallet.
pub fn multi_block_events() -> Vec<crate::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::MultiBlock(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

/// get the events of the verifier pallet.
pub fn verifier_events() -> Vec<crate::verifier::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::VerifierPallet(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

/// proceed block number to `n`.
pub fn roll_to(n: BlockNumber) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);

		MultiBlock::on_initialize(i);
		VerifierPallet::on_initialize(i);
		UnsignedPallet::on_initialize(i);

		if matches!(SignedPhaseSwitch::get(), SignedSwitch::Real) {
			SignedPallet::on_initialize(i);
		}

		// invariants must hold at the end of each block.
		all_pallets_sanity_checks()
	}
}

/// proceed block number to whenever the snapshot is fully created (`Phase::Snapshot(0)`).
pub fn roll_to_snapshot_created() {
	while !matches!(MultiBlock::current_phase(), Phase::Snapshot(0)) {
		roll_next()
	}
	assert_full_snapshot();
}

/// proceed block number to whenever the unsigned phase is open (`Phase::Unsigned(_)`).
pub fn roll_to_unsigned_open() {
	while !matches!(MultiBlock::current_phase(), Phase::Unsigned(_)) {
		roll_next()
	}
}

/// proceed block number to whenever the signed phase is open (`Phase::Signed(_)`).
pub fn roll_to_signed_open() {
	while !matches!(MultiBlock::current_phase(), Phase::Signed) {
		roll_next();
	}
}

/// proceed block number to whenever the signed validation phase is open
/// (`Phase::SignedValidation(_)`).
pub fn roll_to_signed_validation_open() {
	while !matches!(MultiBlock::current_phase(), Phase::SignedValidation(_)) {
		roll_next()
	}
}

/// Proceed one block.
pub fn roll_next() {
	roll_to(System::block_number() + 1);
}

/// Proceed one block, and execute offchain workers as well.
pub fn roll_next_with_ocw(maybe_pool: Option<Arc<RwLock<PoolState>>>) {
	roll_to_with_ocw(System::block_number() + 1, maybe_pool)
}

/// proceed block number to `n`, while running all offchain workers as well.
pub fn roll_to_with_ocw(n: BlockNumber, maybe_pool: Option<Arc<RwLock<PoolState>>>) {
	use sp_runtime::traits::Dispatchable;
	let now = System::block_number();
	for i in now + 1..=n {
		// check the offchain transaction pool, and if anything's there, submit it.
		if let Some(ref pool) = maybe_pool {
			pool.read()
				.transactions
				.clone()
				.into_iter()
				.map(|uxt| <Extrinsic as codec::Decode>::decode(&mut &*uxt).unwrap())
				.for_each(|xt| {
					xt.call.dispatch(frame_system::RawOrigin::None.into()).unwrap();
				});
			pool.try_write().unwrap().transactions.clear();
		}

		System::set_block_number(i);

		MultiBlock::on_initialize(i);
		VerifierPallet::on_initialize(i);
		UnsignedPallet::on_initialize(i);
		if matches!(SignedPhaseSwitch::get(), SignedSwitch::Real) {
			SignedPallet::on_initialize(i);
		}

		MultiBlock::offchain_worker(i);
		VerifierPallet::offchain_worker(i);
		UnsignedPallet::offchain_worker(i);
		if matches!(SignedPhaseSwitch::get(), SignedSwitch::Real) {
			SignedPallet::offchain_worker(i);
		}

		// invariants must hold at the end of each block.
		all_pallets_sanity_checks()
	}
}

/// An invalid solution with any score.
pub fn fake_solution(score: ElectionScore) -> PagedRawSolution<Runtime> {
	PagedRawSolution {
		score,
		solution_pages: bounded_vec![Default::default()],
		..Default::default()
	}
}

/// A real solution that's valid, but has a really bad score.
///
/// This is different from `solution_from_supports` in that it does not require the snapshot to
/// exist.
// TODO: probably deprecate this.
pub fn raw_paged_solution_low_score() -> PagedRawSolution<Runtime> {
	PagedRawSolution {
		solution_pages: vec![TestNposSolution {
			// 2 targets, both voting for themselves
			votes1: vec![(0, 0), (1, 2)],
			..Default::default()
		}]
		.try_into()
		.unwrap(),
		round: 0,
		score: ElectionScore { minimal_stake: 10, sum_stake: 20, sum_stake_squared: 200 },
	}
}

/// Get the free and reserved balance of `who`.
pub fn balances(who: AccountId) -> (Balance, Balance) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}
