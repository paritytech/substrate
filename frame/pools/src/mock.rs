use super::*;
use crate::{self as pools};
use frame_support::parameter_types;

pub type AccountId = u32;
pub type Balance = u32;

parameter_types! {
	static CurrentEra: EraIndex = 0;
	static BondedBalance: Balance = 0;
}

pub struct StakingMock;
impl sp_staking::StakingInterface for StakingMock {
	type Balance = Balance;
	type AccountId = AccountId;

	fn minimum_bond() -> Self::Balance {
		10
	}

	fn current_era() -> EraIndex {
		CurrentEra::get()
	}

	fn bonding_duration() -> EraIndex {
		3
	}

	fn bonded_balance(_: &Self::AccountId) -> Self::Balance {
		BondedBalance::get()
	}

	fn bond_extra(_: &Self::AccountId, _: Self::Balance) -> DispatchResult {
		Ok(())
	}

	fn unbond(_: &Self::AccountId, _: Self::Balance) -> DispatchResult {
		Ok(())
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
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
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub static ExistentialDeposit: Balance = 1;
}

impl pallet_balances::Config for Runtime {
	type MaxLocks = frame_support::traits::ConstU32<1024>;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub static MaxUnbonding: u32 = 5;
}

pub struct BalanceToU128;
impl Convert<Balance, u128> for BalanceToU128 {
	fn convert(n: Balance) -> u128 {
		n as u128
	}
}

pub struct U128ToBalance;
impl Convert<u128, Balance> for U128ToBalance {
	fn convert(n: u128) -> Balance {
		if n > Balance::MAX as u128 {
			Balance::MAX
		} else {
			n as Balance
		}
	}
}

impl pools::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type BalanceToU128 = BalanceToU128;
	type U128ToBalance = U128ToBalance;
	type StakingInterface = StakingMock;
	type MaxUnbonding = MaxUnbonding;
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
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Pools: pools::{Pallet, Call, Storage, Event<T>},
	}
);
