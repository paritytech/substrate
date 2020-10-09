use super::*;
use frame_support::{parameter_types, traits::OnInitialize};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
use std::cell::RefCell;

pub use frame_support::{assert_noop, assert_ok};

#[derive(Eq, PartialEq, Clone)]
pub struct Runtime;
pub(crate) type Balances = pallet_balances::Module<Runtime>;
pub(crate) type System = frame_system::Module<Runtime>;
pub(crate) type TwoPhase = super::Module<Runtime>;
pub(crate) type Balance = u64;
pub(crate) type AccountId = u64;

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
pub fn raw_solution() -> RawSolution {
	let voters = TwoPhase::snapshot_voters().unwrap();
	let targets = TwoPhase::snapshot_targets().unwrap();
	let desired = TwoPhase::desired_targets() as usize;

	// closures
	let voter_index = crate::voter_index_fn!(voters, AccountId);
	let target_index = crate::target_index_fn!(targets, AccountId);
	let stake_of = crate::stake_of_fn!(voters, AccountId);

	use sp_npos_elections::{seq_phragmen, to_without_backing, ElectionResult};
	let ElectionResult {
		winners,
		assignments,
	} = seq_phragmen::<_, OffchainAccuracy>(desired, targets.clone(), voters.clone(), None).unwrap();

	let winners = to_without_backing(winners);

	let score = {
		// TODO: we really need to clean this process.
		let staked = sp_npos_elections::assignment_ratio_to_staked(assignments.clone(), &stake_of);
		let support = sp_npos_elections::build_support_map(&winners, &staked).unwrap();
		sp_npos_elections::evaluate_support(&support)
	};
	let compact =
		CompactAssignments::from_assignment(assignments, &voter_index, &target_index).unwrap();
	let winners = winners
		.into_iter()
		.map(|w| target_index(&w).unwrap())
		.collect::<Vec<_>>();

	RawSolution {
		winners,
		compact,
		score,
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
	type Call = ();
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
}

impl crate::two_phase::Trait for Runtime {
	type Event = ();
	type Currency = Balances;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type MaxSignedSubmissions = MaxSignedSubmissions;
	type SignedRewardBase = SignedRewardBase;
	type SignedRewardFactor = ();
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SolutionImprovementThreshold = ();
	type SlashHandler = ();
	type RewardHandler = ();
	type ElectionDataProvider = ExtBuilder;
	type WeightInfo = ();
}

pub struct ExtBuilder {
	max_signed_submissions: u32,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			max_signed_submissions: MaxSignedSubmissions::get(),
		}
	}
}

impl crate::ElectionDataProvider<AccountId, u64> for ExtBuilder {
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
	fn set_constants(&self) {
		MAX_SIGNED_SUBMISSIONS.with(|v| *v.borrow_mut() = self.max_signed_submissions)
	}
	pub(crate) fn max_signed_submission(mut self, count: u32) -> Self {
		self.max_signed_submissions = count;
		self
	}
	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.set_constants();
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

		sp_io::TestExternalities::from(storage).execute_with(test)
	}
}
