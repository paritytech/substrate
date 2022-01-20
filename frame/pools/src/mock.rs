use super::*;
use crate::{self as pools};
use frame_support::{assert_ok, parameter_types};
use frame_system::RawOrigin;

pub type AccountId = u32;
pub type Balance = u32;

/// Pool 0's primary account id (i.e. its stash and controller account).
pub const PRIMARY_ACCOUNT: u32 = 2536596763;
/// Pool 0's reward destination.
pub const REWARDS_ACCOUNT: u32 = 736857005;

parameter_types! {
	static CurrentEra: EraIndex = 0;
	pub static BondedBalanceMap: std::collections::HashMap<AccountId, Balance> = Default::default();
}

pub struct StakingMock;
impl StakingMock {
	fn set_bonded_balance(who: AccountId, bonded: Balance) {
		BONDED_BALANCE_MAP.with(|m| m.borrow_mut().insert(who.clone(), bonded));
	}
}

impl sp_staking::StakingInterface for StakingMock {
	type Balance = Balance;
	type AccountId = AccountId;
	type LookupSource = Self::AccountId;

	fn minimum_bond() -> Self::Balance {
		10
	}

	fn current_era() -> EraIndex {
		CurrentEra::get()
	}

	fn bonding_duration() -> EraIndex {
		3
	}

	fn bonded_balance(who: &Self::AccountId) -> Self::Balance {
		BondedBalanceMap::get().get(who).map(|v| *v).unwrap_or_default()
	}

	fn bond_extra(who: &Self::AccountId, extra: Self::Balance) -> DispatchResult {
		// Simulate bond extra in `join`
		BONDED_BALANCE_MAP.with(|m| *m.borrow_mut().get_mut(who).unwrap() += extra);
		Ok(())
	}

	fn unbond(who: &Self::AccountId, amount: Self::Balance) -> DispatchResult {
		BONDED_BALANCE_MAP.with(|m| *m.borrow_mut().get_mut(who).unwrap() -= amount);
		Ok(())
	}

	fn bond(
		stash: Self::AccountId,
		_: Self::AccountId,
		amount: Self::Balance,
		_: Self::AccountId,
	) -> DispatchResult {
		StakingMock::set_bonded_balance(stash, amount);
		Ok(())
	}

	fn nominate(_: Self::AccountId, _: Vec<Self::LookupSource>) -> DispatchResult {
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

parameter_types! {
	pub static MaxUnbonding: u32 = 5;
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

#[derive(Default)]
pub struct ExtBuilder {
	delegators: Vec<(AccountId, Balance)>,
}

impl ExtBuilder {
	// Add delegators to pool 0.
	pub(crate) fn add_delegators(mut self, delegators: Vec<(AccountId, Balance)>) -> Self {
		self.delegators = delegators;
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let storage = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let mut ext = sp_io::TestExternalities::from(storage);

		ext.execute_with(|| {
			// make a pool
			let amount_to_bond = <Runtime as pools::Config>::StakingInterface::minimum_bond();
			Balances::make_free_balance_be(&10, amount_to_bond * 2);

			assert_ok!(Pools::create(RawOrigin::Signed(10).into(), 0, vec![100], amount_to_bond));
			for (account_id, bonded) in self.delegators {
				Balances::make_free_balance_be(&account_id, bonded * 2);

				assert_ok!(Pools::join(RawOrigin::Signed(account_id).into(), bonded, 0));
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			// post-checks can be added here
		})
	}
}
