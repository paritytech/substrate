#![cfg(test)]

use frame_support::impl_outer_origin;
use sp_core::H256;
use sp_runtime::traits::IdentityLookup;
use std::cell::RefCell;
use sp_runtime::Perbill;
use sp_runtime::curve::PiecewiseLinear;
use sp_runtime::traits::{Convert};
use sp_runtime::testing::{Header, TestXt};
use frame_support::{
	parameter_types, impl_outer_dispatch,
	weights::{Weight, constants::RocksDbWeight},
};
use logging_timer::timer;
use sp_npos_elections::{
	ElectionResult as PrimitiveElectionResult, assignment_ratio_to_staked_normalized, VoteWeight,
};
use pallet_staking::{Validators, Nominators, Nominations, SlashingSpans};
use frame_support::storage::{IterableStorageMap, StorageMap};

pub struct CurrencyToVoteHandler;

impl CurrencyToVoteHandler {
	fn factor() -> Balance { (Balances::total_issuance() / u64::max_value() as Balance).max(1) }
}

impl Convert<Balance, u64> for CurrencyToVoteHandler {
	fn convert(x: Balance) -> u64 { (x / Self::factor()) as u64 }
}

impl Convert<u128, Balance> for CurrencyToVoteHandler {
	fn convert(x: u128) -> Balance { x * Self::factor() }
}

macro_rules! init_log {
	() => {
		let _ = env_logger::Builder::from_default_env()
			.filter_level(log::LevelFilter::Debug)
			.format_module_path(true)
			.format_level(true)
			.try_init();
	};
}

pub(crate) type AccountId = sp_core::crypto::AccountId32;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u128;

pub(crate) type Session = pallet_session::Module<Runtime>;
pub(crate) type Timestamp = pallet_timestamp::Module<Runtime>;
pub(crate) type Staking = pallet_staking::Module<Runtime>;
pub(crate) type Balances = pallet_balances::Module<Runtime>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Runtime;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl_outer_origin! {
	pub enum Origin for Runtime where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Runtime where origin: Origin {
		staking::Staking,
	}
}

impl frame_system::Trait for Runtime {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u32;
	type BlockNumber = BlockNumber;
	type Call = Call;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = RocksDbWeight;
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl pallet_balances::Trait for Runtime {
	type Balance = Balance;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ();
	type AccountStore = frame_system::Module<Runtime>;
	type WeightInfo = ();
}

parameter_types! {
	pub const MinimumPeriod: u64 = 5;
}
impl pallet_timestamp::Trait for Runtime {
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}

parameter_types! {
	pub const UncleGenerations: u64 = 0;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(25);
}

sp_runtime::impl_opaque_keys! {
	pub struct SessionKeys {}
}

pub struct TestSessionHandler;
impl pallet_session::SessionHandler<AccountId> for TestSessionHandler {
	const KEY_TYPE_IDS: &'static [sp_runtime::KeyTypeId] = &[];

	fn on_genesis_session<Ks: sp_runtime::traits::OpaqueKeys>(_validators: &[(AccountId, Ks)]) {}

	fn on_new_session<Ks: sp_runtime::traits::OpaqueKeys>(
		_: bool,
		_: &[(AccountId, Ks)],
		_: &[(AccountId, Ks)],
	) {}

	fn on_disabled(_: usize) {}
}


impl pallet_session::Trait for Runtime {
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Self, Staking>;
	type Keys = SessionKeys;
	type ShouldEndSession = pallet_session::PeriodicSessions<(), ()>;
	type SessionHandler = TestSessionHandler;
	type Event = ();
	type ValidatorId = <Self as frame_system::Trait>::AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Self>;
	type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
	type NextSessionRotation = pallet_session::PeriodicSessions<(), ()>;
	type WeightInfo = ();
}

impl pallet_session::historical::Trait for Runtime {
	type FullIdentification = pallet_staking::Exposure<<Self as frame_system::Trait>::AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Self>;
}

pallet_staking_reward_curve::build! {
	const I_NPOS: PiecewiseLinear<'static> = curve!(
		min_inflation: 0_025_000,
		max_inflation: 0_100_000,
		ideal_stake: 0_500_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}

parameter_types! {
	pub const BondingDuration: u32 = 3;
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &I_NPOS;
	pub const MaxNominatorRewardedPerValidator: u32 = 64;
	pub const UnsignedPriority: u64 = 1 << 20;
	pub const MinSolutionScoreBump: Perbill = Perbill::zero();
}

thread_local! {
	pub static REWARD_REMAINDER_UNBALANCED: RefCell<u128> = RefCell::new(0);
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Runtime where
	Call: From<LocalCall>,
{
	type OverarchingCall = Call;
	type Extrinsic = Extrinsic;
}

pub type Extrinsic = TestXt<Call, ()>;

impl pallet_staking::Trait for Runtime {
	type Currency = pallet_balances::Module<Runtime>;
	type UnixTime = Timestamp;
	type CurrencyToVote = CurrencyToVoteHandler;
	type RewardRemainder = ();
	type Event = ();
	type Slash = ();
	type Reward = ();
	type SessionsPerEra = ();
	type SlashDeferDuration = ();
	type SlashCancelOrigin = frame_system::EnsureRoot<<Self as frame_system::Trait>::AccountId>;
	type BondingDuration = BondingDuration;
	type SessionInterface = Self;
	type RewardCurve = RewardCurve;
	type NextNewSession = Session;
	type ElectionLookahead = ();
	type Call = Call;
	type MaxIterations = ();
	type MinSolutionScoreBump = MinSolutionScoreBump;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type UnsignedPriority = UnsignedPriority;
	type WeightInfo = ();
}

#[test]
fn test_phragmms_phragmen() {
	init_log!();
	let test_block = hex_literal::hex!["82cddc9262057360541568f4bc70ab633db4cf2bb74665201cd786f1b11d9104"];
	remote_externalities::Builder::new()
		.module("Staking")
		.at(test_block.into())
		.build()
		.execute_with(|| {
			let mut all_nominators: Vec<(AccountId, VoteWeight, Vec<AccountId>)> = Vec::new();
			let mut all_validators = Vec::new();
			for (validator, _) in <Validators<Runtime>>::iter() {
				// append self vote
				let self_vote = (validator.clone(), Staking::slashable_balance_of_vote_weight(&validator), vec![validator.clone()]);
				all_nominators.push(self_vote);
				all_validators.push(validator);
			}

			let nominator_votes = <Nominators<Runtime>>::iter().map(|(nominator, nominations)| {
				let Nominations { submitted_in, mut targets, suppressed: _ } = nominations;

				// Filter out nomination targets which were nominated before the most recent
				// slashing span.
				targets.retain(|stash| {
					<SlashingSpans<Runtime>>::get(&stash).map_or(
						true,
						|spans| submitted_in >= spans.last_nonzero_slash(),
					)
				});

				(nominator, targets)
			});
			all_nominators.extend(nominator_votes.map(|(n, ns)| {
				let s = Staking::slashable_balance_of_vote_weight(&n);
				(n, s, ns)
			}));

			println!("{} validators {} nominators", all_validators.len(), all_nominators.len());

			let time = timer!("phragmms");
			let phragmms_score = {
				let PrimitiveElectionResult { winners, assignments } = sp_npos_elections::phragmms::<AccountId, sp_runtime::Perquintill>(
					Staking::validator_count() as usize,
					all_validators.clone(),
					all_nominators.clone(),
				).unwrap();

				let winners = sp_npos_elections::to_without_backing(winners);

				let staked = assignment_ratio_to_staked_normalized(
					assignments,
					Staking::slashable_balance_of_vote_weight,
				).unwrap();

				let (support, _) = sp_npos_elections::build_support_map::<AccountId>(winners.as_ref(), staked.as_ref());
				// dbg!(&support);
				sp_npos_elections::evaluate_support(&support)
			};
			drop(time);

			let time = timer!("phragmen");
			let phragmen_score = {
				let PrimitiveElectionResult { winners, assignments } = sp_npos_elections::seq_phragmen::<AccountId, Perbill>(
					Staking::validator_count() as usize,
					all_validators.clone(),
					all_nominators.clone(),
					Some((10, 0)),
				).unwrap();

				let winners = sp_npos_elections::to_without_backing(winners);

				let staked = assignment_ratio_to_staked_normalized(
					assignments,
					Staking::slashable_balance_of_vote_weight,
				).unwrap();

				let (support, _) = sp_npos_elections::build_support_map::<AccountId>(winners.as_ref(), staked.as_ref());
				sp_npos_elections::evaluate_support(&support)
			};
			drop(time);

			dbg!(phragmen_score, phragmms_score);
			assert!(sp_npos_elections::is_score_better(phragmms_score, phragmen_score, Perbill::zero()));

			assert!(false);
		});
}
