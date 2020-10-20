use super::*;
use frame_support::{parameter_types, traits::OnInitialize};
use parking_lot::RwLock;
use rand::seq::SliceRandom;
use sp_core::{
	offchain::{
		testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
		OffchainExt, TransactionPoolExt,
	},
	H256,
};
use sp_election_providers::ElectionDataProvider;
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, seq_phragmen, to_supports, to_without_backing,
	Assignment, CompactSolution, ElectionResult, EvaluateSupport,
};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16,
};
use std::{cell::RefCell, sync::Arc};

pub use frame_support::{assert_noop, assert_ok};

#[derive(Eq, PartialEq, Clone)]
pub struct Runtime;
pub(crate) type Balances = pallet_balances::Module<Runtime>;
pub(crate) type System = frame_system::Module<Runtime>;
pub(crate) type TwoPhase = super::Module<Runtime>;
pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct TestCompact::<u32, u16, PerU16>(16)
);

/// To from `now` to block `n`.
pub fn roll_to(n: u64) {
	let now = System::block_number();
	for i in now + 1..=n {
		System::set_block_number(i);
		TwoPhase::on_initialize(i);
	}
}

/// Get the free and reserved balance of some account.
pub fn balances(who: &AccountId) -> (Balance, Balance) {
	(Balances::free_balance(who), Balances::reserved_balance(who))
}

/// Spit out a verifiable raw solution.
///
/// This is a good example of what an offchain miner would do.
pub fn raw_solution() -> RawSolution<CompactOf<Runtime>> {
	let voters = TwoPhase::snapshot_voters().unwrap();
	let targets = TwoPhase::snapshot_targets().unwrap();
	let desired = TwoPhase::desired_targets() as usize;

	// closures
	let voter_index = crate::voter_index_fn!(voters, AccountId, Runtime);
	let target_index = crate::target_index_fn!(targets, AccountId, Runtime);
	let stake_of = crate::stake_of_fn!(voters, AccountId);

	let ElectionResult {
		winners,
		assignments,
	} = seq_phragmen::<_, CompactAccuracyOf<Runtime>>(desired, targets.clone(), voters.clone(), None)
		.unwrap();

	let winners = to_without_backing(winners);

	let score = {
		let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of).unwrap();
		to_supports(&winners, &staked).unwrap().evaluate()
	};
	let compact =
		<CompactOf<Runtime>>::from_assignment(assignments, &voter_index, &target_index).unwrap();

	RawSolution { compact, score }
}

frame_support::impl_outer_dispatch! {
	pub enum OuterCall for Runtime where origin: Origin {
		two_phase::TwoPhase,
	}
}

frame_support::impl_outer_origin! {
	pub enum Origin for Runtime where system = frame_system {}
}

impl frame_system::Trait for Runtime {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = OuterCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = ();
	type MaximumBlockWeight = ();
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = ();
	type MaximumBlockLength = ();
	type AvailableBlockRatio = ();
	type Version = ();
	type PalletInfo = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Trait for Runtime {
	type Balance = Balance;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ();
	type WeightInfo = ();
}

use paste::paste;
macro_rules! parameter_types_thread_local {
	(
		$(
			static $name:ident : $type:ty = $default:expr;
		)*
	) => {
		parameter_types_thread_local! {
			@THREAD_LOCAL($(
				$name, $type, $default,
			)*)
		}

		parameter_types_thread_local! {
			@GETTER_STRUCT($(
				$name, $type,
			)*)
		}
	};
	(@THREAD_LOCAL($($name:ident, $type:ty, $default:expr,)*)) => {
		thread_local! {
			$(
				static $name: RefCell<$type> = RefCell::new($default);
			)*
		}
	};
	(@GETTER_STRUCT($($name:ident, $type:ty,)*)) => {
		$(
			paste! {
				pub struct [<$name:camel>];
				impl Get<$type> for [<$name:camel>] {
					fn get() -> $type { $name.with(|v| v.borrow().clone() )}
				}
			}
		)*
	}
}

parameter_types_thread_local! {
	static SIGNED_PHASE: u64 = 10;
	static UNSIGNED_PHASE: u64 = 5;
	static MAX_SIGNED_SUBMISSIONS: u32 = 5;
	static TARGETS: Vec<AccountId> = vec![10, 20, 30, 40];
	static VOTERS: Vec<(AccountId, VoteWeight, Vec<AccountId>)> = vec![
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
	static DESIRED_TARGETS: u32 = 2;
	static SIGNED_DEPOSIT_BASE: Balance = 5;
	static SIGNED_REWARD_BASE: Balance = 7;
	static MAX_UNSIGNED_ITERATIONS: u32 = 5;
	static UNSIGNED_PRIORITY: u64 = 100;
	static SOLUTION_IMPROVEMENT_THRESHOLD: Perbill = Perbill::zero();
}

impl crate::two_phase::Trait for Runtime {
	type Event = ();
	type Currency = Balances;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type MaxSignedSubmissions = MaxSignedSubmissions;
	type SignedRewardBase = SignedRewardBase;
	type SignedRewardFactor = ();
	type SignedRewardMax = ();
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type SlashHandler = ();
	type RewardHandler = ();
	type UnsignedMaxIterations = MaxUnsignedIterations;
	type UnsignedPriority = UnsignedPriority;
	type ElectionDataProvider = StakingMock;
	type WeightInfo = ();
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	OuterCall: From<LocalCall>,
{
	type OverarchingCall = OuterCall;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = sp_runtime::testing::TestXt<OuterCall, ()>;

pub struct ExtBuilder {}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {}
	}
}

pub struct StakingMock;
impl ElectionDataProvider<AccountId, u64> for StakingMock {
	type CompactSolution = TestCompact;

	fn targets() -> Vec<AccountId> {
		Targets::get()
	}
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
		Voters::get()
	}
	fn desired_targets() -> u32 {
		DesiredTargets::get()
	}
	fn feasibility_check_assignment<P: PerThing>(_: &AccountId, _: &[(AccountId, P)]) -> bool {
		true
	}
	fn next_election_prediction(now: u64) -> u64 {
		now + 20 - now % 20
	}
}

impl ExtBuilder {
	pub fn max_signed_submission(self, count: u32) -> Self {
		MAX_SIGNED_SUBMISSIONS.with(|v| *v.borrow_mut() = count);
		self
	}
	pub fn unsigned_priority(self, p: u64) -> Self {
		UNSIGNED_PRIORITY.with(|v| *v.borrow_mut() = p);
		self
	}
	pub fn solution_improvement_threshold(self, p: Perbill) -> Self {
		SOLUTION_IMPROVEMENT_THRESHOLD.with(|v| *v.borrow_mut() = p);
		self
	}
	pub fn desired_targets(self, t: u32) -> Self {
		DESIRED_TARGETS.with(|v| *v.borrow_mut() = t);
		self
	}
	pub fn add_voter(self, who: AccountId, stake: Balance, targets: Vec<AccountId>) -> Self {
		VOTERS.with(|v| v.borrow_mut().push((who, stake, targets)));
		self
	}
	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage = frame_system::GenesisConfig::default()
			.build_storage::<Runtime>()
			.unwrap();

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

		ext.register_extension(OffchainExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		(ext, pool_state)
	}
	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}
