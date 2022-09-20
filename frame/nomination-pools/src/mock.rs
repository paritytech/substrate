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
	pub static BondingDuration: EraIndex = 3;
	pub storage BondedBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	pub storage UnbondingBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	#[derive(Clone, PartialEq)]
	pub static MaxUnbonding: u32 = 8;
	pub storage Nominations: Option<Vec<AccountId>> = None;
}

pub struct StakingMock;
impl StakingMock {
	pub(crate) fn set_bonded_balance(who: AccountId, bonded: Balance) {
		let mut x = BondedBalanceMap::get();
		x.insert(who, bonded);
		BondedBalanceMap::set(&x)
	}
}

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
		BondingDuration::get()
	}

	fn active_stake(who: &Self::AccountId) -> Option<Self::Balance> {
		BondedBalanceMap::get().get(who).map(|v| *v)
	}

	fn total_stake(who: &Self::AccountId) -> Option<Self::Balance> {
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
		let mut x = BondedBalanceMap::get();
		x.get_mut(&who).map(|v| *v += extra);
		BondedBalanceMap::set(&x);
		Ok(())
	}

	fn unbond(who: Self::AccountId, amount: Self::Balance) -> DispatchResult {
		let mut x = BondedBalanceMap::get();
		*x.get_mut(&who).unwrap() = x.get_mut(&who).unwrap().saturating_sub(amount);
		BondedBalanceMap::set(&x);
		let mut y = UnbondingBalanceMap::get();
		*y.entry(who).or_insert(Self::Balance::zero()) += amount;
		UnbondingBalanceMap::set(&y);
		Ok(())
	}

	fn chill(_: Self::AccountId) -> sp_runtime::DispatchResult {
		Ok(())
	}

	fn withdraw_unbonded(who: Self::AccountId, _: u32) -> Result<bool, DispatchError> {
		// Simulates removing unlocking chunks and only having the bonded balance locked
		let mut x = UnbondingBalanceMap::get();
		x.remove(&who);
		UnbondingBalanceMap::set(&x);

		Ok(UnbondingBalanceMap::get().is_empty() && BondedBalanceMap::get().is_empty())
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

	fn nominate(_: Self::AccountId, nominations: Vec<Self::AccountId>) -> DispatchResult {
		Nominations::set(&Some(nominations));
		Ok(())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn nominations(_: Self::AccountId) -> Option<Vec<Self::AccountId>> {
		Nominations::get()
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
	pub static CheckLevel: u8 = 255;
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
	type MaxUnbonding = MaxUnbonding;
	type MinPointsToBalance = frame_support::traits::ConstU32<10>;
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
	members: Vec<(AccountId, Balance)>,
}

impl ExtBuilder {
	// Add members to pool 0.
	pub(crate) fn add_members(mut self, members: Vec<(AccountId, Balance)>) -> Self {
		self.members = members;
		self
	}

	pub(crate) fn ed(self, ed: Balance) -> Self {
		ExistentialDeposit::set(ed);
		self
	}

	pub(crate) fn with_check(self, level: u8) -> Self {
		CheckLevel::set(level);
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		let mut storage =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let _ = crate::GenesisConfig::<Runtime> {
			min_join_bond: 2,
			min_create_bond: 2,
			max_pools: Some(2),
			max_members_per_pool: Some(3),
			max_members: Some(4),
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		ext.execute_with(|| {
			// for events to be deposited.
			frame_system::Pallet::<Runtime>::set_block_number(1);

			// make a pool
			let amount_to_bond = <Runtime as pools::Config>::StakingInterface::minimum_bond();
			Balances::make_free_balance_be(&10, amount_to_bond * 2);
			assert_ok!(Pools::create(RawOrigin::Signed(10).into(), amount_to_bond, 900, 901, 902));

			let last_pool = LastPoolId::<Runtime>::get();
			for (account_id, bonded) in self.members {
				Balances::make_free_balance_be(&account_id, bonded * 2);
				assert_ok!(Pools::join(RawOrigin::Signed(account_id).into(), bonded, last_pool));
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			Pools::sanity_checks(CheckLevel::get()).unwrap();
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

parameter_types! {
	static PoolsEvents: usize = 0;
	static BalancesEvents: usize = 0;
}

/// All events of this pallet.
pub(crate) fn pool_events_since_last_call() -> Vec<super::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::Pools(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = PoolsEvents::get();
	PoolsEvents::set(events.len());
	events.into_iter().skip(already_seen).collect()
}

/// All events of the `Balances` pallet.
pub(crate) fn balances_events_since_last_call() -> Vec<pallet_balances::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::Balances(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = BalancesEvents::get();
	BalancesEvents::set(events.len());
	events.into_iter().skip(already_seen).collect()
}

/// Same as `fully_unbond`, in permissioned setting.
pub fn fully_unbond_permissioned(member: AccountId) -> DispatchResult {
	let points = PoolMembers::<Runtime>::get(&member)
		.map(|d| d.active_points())
		.unwrap_or_default();
	Pools::unbond(Origin::signed(member), member, points)
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
