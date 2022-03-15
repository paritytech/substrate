use super::*;
use crate::{self as pools};
use frame_support::{assert_ok, parameter_types, PalletId};
use frame_system::RawOrigin;

pub type AccountId = u128;
pub type Balance = u128;

// Ext builder creates a pool with id 1.
pub fn default_bonded_account() -> AccountId {
	Pools::create_bonded_account(1)
}

// Ext builder creates a pool with id 1.
pub fn default_reward_account() -> AccountId {
	Pools::create_reward_account(1)
}

parameter_types! {
	pub static CurrentEra: EraIndex = 0;
	static BondedBalanceMap: std::collections::HashMap<AccountId, Balance> = Default::default();
	static UnbondingBalanceMap: std::collections::HashMap<AccountId, Balance> = Default::default();
	pub static BondingDuration: EraIndex = 3;
	pub static Nominations: Vec<AccountId> = vec![];
}

pub struct StakingMock;
impl StakingMock {
	pub(crate) fn set_bonded_balance(who: AccountId, bonded: Balance) {
		BONDED_BALANCE_MAP.with(|m| m.borrow_mut().insert(who, bonded));
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
		BondingDuration::get()
	}

	fn bonded_balance(who: &Self::AccountId) -> Option<Self::Balance> {
		BondedBalanceMap::get().get(who).map(|v| *v)
	}

	fn locked_balance(who: &Self::AccountId) -> Option<Self::Balance> {
		match (
			UnbondingBalanceMap::get().get(who).map(|v| *v),
			BondedBalanceMap::get().get(who).map(|v| *v),
		) {
			(None, None) => None,
			(Some(v), None) | (None, Some(v)) => Some(v),
			(Some(a), Some(b)) => Some(a + b),
		}
	}

	fn bond_extra(who: Self::AccountId, extra: Self::Balance) -> DispatchResult {
		BONDED_BALANCE_MAP.with(|m| *m.borrow_mut().get_mut(&who).unwrap() += extra);
		Ok(())
	}

	fn unbond(who: Self::AccountId, amount: Self::Balance) -> DispatchResult {
		BONDED_BALANCE_MAP.with(|m| *m.borrow_mut().get_mut(&who).unwrap() -= amount);
		UNBONDING_BALANCE_MAP
			.with(|m| *m.borrow_mut().entry(who).or_insert(Self::Balance::zero()) += amount);
		Ok(())
	}

	fn withdraw_unbonded(who: Self::AccountId, _: u32) -> Result<u64, DispatchError> {
		// Simulates removing unlocking chunks and only having the bonded balance locked
		let _maybe_new_free = UNBONDING_BALANCE_MAP.with(|m| m.borrow_mut().remove(&who));

		Ok(100)
	}

	fn bond(
		stash: Self::AccountId,
		_: Self::AccountId,
		value: Self::Balance,
		_: Self::AccountId,
	) -> DispatchResult {
		StakingMock::set_bonded_balance(stash, value);
		Ok(())
	}

	fn nominate(_: Self::AccountId, nominations: Vec<Self::LookupSource>) -> DispatchResult {
		Nominations::set(nominations);
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
	pub static ExistentialDeposit: Balance = 5;
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

pub struct BalanceToU256;
impl Convert<Balance, U256> for BalanceToU256 {
	fn convert(n: Balance) -> U256 {
		n.into()
	}
}

pub struct U256ToBalance;
impl Convert<U256, Balance> for U256ToBalance {
	fn convert(n: U256) -> Balance {
		n.try_into().unwrap()
	}
}

parameter_types! {
	pub static PostUnbondingPoolsWindow: u32 = 2;
	pub static MaxMetadataLen: u32 = 2;
	pub const PoolsPalletId: PalletId = PalletId(*b"py/nopls");
}
impl pools::Config for Runtime {
	type Event = Event;
	type WeightInfo = ();
	type Currency = Balances;
	type BalanceToU256 = BalanceToU256;
	type U256ToBalance = U256ToBalance;
	type StakingInterface = StakingMock;
	type PostUnbondingPoolsWindow = PostUnbondingPoolsWindow;
	type PalletId = PoolsPalletId;
	type MaxMetadataLen = MaxMetadataLen;
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
		// sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = crate::GenesisConfig::<Runtime> {
			min_join_bond: 2,
			min_create_bond: 2,
			max_pools: Some(2),
			max_delegators_per_pool: Some(3),
			max_delegators: Some(4),
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		ext.execute_with(|| {
			// make a pool
			let amount_to_bond = <Runtime as pools::Config>::StakingInterface::minimum_bond();
			Balances::make_free_balance_be(&10, amount_to_bond * 2);
			assert_ok!(Pools::create(RawOrigin::Signed(10).into(), amount_to_bond, 900, 901, 902));

			let last_pool = LastPoolId::<Runtime>::get();
			for (account_id, bonded) in self.delegators {
				Balances::make_free_balance_be(&account_id, bonded * 2);
				assert_ok!(Pools::join(RawOrigin::Signed(account_id).into(), bonded, last_pool));
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			crate::sanity::checks::<Runtime>();
		})
	}

	pub fn build_and_execute_no_checks(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
		})
	}
}

pub(crate) fn unsafe_set_state(pool_id: PoolId, state: PoolState) -> Result<(), ()> {
	BondedPools::<Runtime>::try_mutate(pool_id, |maybe_bonded_pool| {
		maybe_bonded_pool.as_mut().ok_or(()).map(|bonded_pool| {
			bonded_pool.state = state;
		})
	})
}

#[cfg(test)]
mod test {
	use super::*;
	#[test]
	fn u256_to_balance_convert_works() {
		assert_eq!(U256ToBalance::convert(0u32.into()), Zero::zero());
		assert_eq!(U256ToBalance::convert(Balance::max_value().into()), Balance::max_value())
	}

	#[test]
	#[should_panic]
	fn u256_to_balance_convert_panics_correctly() {
		U256ToBalance::convert(U256::from(Balance::max_value()).saturating_add(1u32.into()));
	}

	#[test]
	fn balance_to_u256_convert_works() {
		assert_eq!(BalanceToU256::convert(0u32.into()), U256::zero());
		assert_eq!(BalanceToU256::convert(Balance::max_value()), Balance::max_value().into())
	}
}
