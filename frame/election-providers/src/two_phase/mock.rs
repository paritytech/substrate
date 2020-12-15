use super::*;
use frame_support::{parameter_types, traits::OnInitialize, weights::Weight};
use parking_lot::RwLock;
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
	CompactSolution, ElectionResult, EvaluateSupport,
};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	PerU16,
};
use std::sync::Arc;

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

/// All events of this pallet.
pub(crate) fn two_phase_events() -> Vec<Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let MetaEvent::two_phase(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect::<Vec<_>>()
}

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
	let RoundSnapshot {
		voters,
		targets,
	} = TwoPhase::snapshot().unwrap();
	let desired_targets = TwoPhase::desired_targets().unwrap();

	// closures
	let voter_index = crate::voter_index_fn!(voters, AccountId, Runtime);
	let target_index = crate::target_index_fn!(targets, AccountId, Runtime);
	let stake_of = crate::stake_of_fn!(voters, AccountId);

	let ElectionResult {
		winners,
		assignments,
	} = seq_phragmen::<_, CompactAccuracyOf<Runtime>>(
		desired_targets as usize,
		targets.clone(),
		voters.clone(),
		None,
	)
	.unwrap();

	let winners = to_without_backing(winners);

	let score = {
		let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of).unwrap();
		to_supports(&winners, &staked).unwrap().evaluate()
	};
	let compact =
		<CompactOf<Runtime>>::from_assignment(assignments, &voter_index, &target_index).unwrap();

	let round = TwoPhase::round();
	RawSolution { compact, score, round }
}

pub fn witness() -> WitnessData {
	TwoPhase::snapshot()
		.map(|snap| WitnessData {
			voters: snap.voters.len() as u32,
			targets: snap.targets.len() as u32,
		})
		.unwrap_or_default()
}

frame_support::impl_outer_dispatch! {
	pub enum OuterCall for Runtime where origin: Origin {
		two_phase::TwoPhase,
	}
}

frame_support::impl_outer_origin! {
	pub enum Origin for Runtime where system = frame_system {}
}

mod two_phase {
	// Re-export needed for `impl_outer_event!`.
	pub use super::super::*;
}
use frame_system as system;
use pallet_balances as balances;

frame_support::impl_outer_event! {
	pub enum MetaEvent for Runtime {
		system<T>,
		balances<T>,
		two_phase<T>,
	}
}

impl frame_system::Config for Runtime {
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
	type Event = MetaEvent;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = ();
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

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type Event = MetaEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = ();
	type WeightInfo = ();
}

parameter_types! {
	pub static SignedPhase: u64 = 10;
	pub static UnsignedPhase: u64 = 5;
	pub static MaxSignedSubmissions: u32 = 5;
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
	pub static DesiredTargets: u32 = 2;
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositByte: Balance = 0;
	pub static SignedDepositWeight: Balance = 0;
	pub static SignedRewardBase: Balance = 7;
	pub static SignedRewardFactor: Perbill = Perbill::zero();
	pub static SignedRewardMax: Balance = 10;
	pub static MinerMaxIterations: u32 = 5;
	pub static UnsignedPriority: u64 = 100;
	pub static SolutionImprovementThreshold: Perbill = Perbill::zero();
	pub static MinerMaxWeight: Weight = 128;
	pub static EpochLength: u64 = 30;
}

impl crate::two_phase::Config for Runtime {
	type Event = MetaEvent;
	type Currency = Balances;
	type SignedPhase = SignedPhase;
	type UnsignedPhase = UnsignedPhase;
	type MaxSignedSubmissions = MaxSignedSubmissions;
	type SignedRewardBase = SignedRewardBase;
	type SignedRewardFactor = SignedRewardFactor;
	type SignedRewardMax = SignedRewardMax;
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = ();
	type SignedDepositWeight = ();
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type SlashHandler = ();
	type RewardHandler = ();
	type MinerMaxIterations = MinerMaxIterations;
	type MinerMaxWeight = MinerMaxWeight;
	type UnsignedPriority = UnsignedPriority;
	type ElectionDataProvider = StakingMock;
	type WeightInfo = ();
	type CompactSolution = TestCompact;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime
where
	OuterCall: From<LocalCall>,
{
	type OverarchingCall = OuterCall;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = sp_runtime::testing::TestXt<OuterCall, ()>;

#[derive(Default)]
pub struct ExtBuilder {}

pub struct StakingMock;
impl ElectionDataProvider<AccountId, u64> for StakingMock {
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
		now + EpochLength::get() - now % EpochLength::get()
	}
}

impl ExtBuilder {
	pub fn max_signed_submission(self, count: u32) -> Self {
		<MaxSignedSubmissions>::set(count);
		self
	}
	pub fn unsigned_priority(self, p: u64) -> Self {
		<UnsignedPriority>::set(p);
		self
	}
	pub fn solution_improvement_threshold(self, p: Perbill) -> Self {
		<SolutionImprovementThreshold>::set(p);
		self
	}
	pub fn signed_deposit(self, base: u64, byte: u64, weight: u64) -> Self {
		<SignedDepositBase>::set(base);
		<SignedDepositByte>::set(byte);
		<SignedDepositWeight>::set(weight);
		self
	}
	pub fn phases(self, signed: u64, unsigned: u64) -> Self {
		<SignedPhase>::set(signed);
		<UnsignedPhase>::set(unsigned);
		self
	}
	pub fn reward(self, base: u64, factor: Perbill, max: u64) -> Self {
		<SignedRewardBase>::set(base);
		<SignedRewardFactor>::set(factor);
		<SignedRewardMax>::set(max);
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
