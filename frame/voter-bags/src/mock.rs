use super::*;
use frame_election_provider_support::VoteWeight;
use frame_support::parameter_types;
use std::cell::RefCell;

type AccountId = u32;
type Balance = u32;

thread_local! {
	static VOTE_WEIGHT: RefCell<VoteWeight> = RefCell::new(Default::default())
}

/// Set a mock return value for `StakingVoteWeight::staking_vote_weight`.
fn set_staking_vote_weight(weight: VoteWeight) {
	VOTE_WEIGHT.with(|w| *w.borrow_mut() = weight);
}

pub struct StakingMock;
impl frame_election_provider_support::StakingVoteWeight<AccountId> for StakingMock {
	fn staking_vote_weight(who: &AccountId) -> VoteWeight {
		VOTE_WEIGHT.with(|h| h.borrow().clone())
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::AllowAll;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

/// Thresholds used for bags.
const THRESHOLDS: [VoteWeight; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub const VoterBagThresholds: &'static [VoteWeight] = &THRESHOLDS;
}

impl crate::Config for Runtime {
	type Event = Event;
	type VoterBagThresholds = VoterBagThresholds;
	type StakingVoteWeight = StakingMock;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Event<T>, Config},
		VoterBags: crate::{Pallet, Call, Storage, Event<T>},
	}
);
