use super::*;
use crate::{self as pools};
use frame_support::{assert_ok, parameter_types, PalletId};
use frame_system::RawOrigin;
use sp_runtime::{BuildStorage, FixedU128};
use sp_staking::Stake;

pub type BlockNumber = u64;
pub type AccountId = u128;
pub type Balance = u128;
pub type RewardCounter = FixedU128;
// This sneaky little hack allows us to write code exactly as we would do in the pallet in the tests
// as well, e.g. `StorageItem::<T>::get()`.
pub type T = Runtime;

// Ext builder creates a pool with id 1.
pub fn default_bonded_account() -> AccountId {
	Pools::create_bonded_account(1)
}

// Ext builder creates a pool with id 1.
pub fn default_reward_account() -> AccountId {
	Pools::create_reward_account(1)
}

parameter_types! {
	pub static MinJoinBondConfig: Balance = 2;
	pub static CurrentEra: EraIndex = 0;
	pub static BondingDuration: EraIndex = 3;
	pub storage BondedBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	pub storage UnbondingBalanceMap: BTreeMap<AccountId, Balance> = Default::default();
	#[derive(Clone, PartialEq)]
	pub static MaxUnbonding: u32 = 8;
	pub static StakingMinBond: Balance = 10;
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
	type CurrencyToVote = ();

	fn minimum_nominator_bond() -> Self::Balance {
		StakingMinBond::get()
	}
	fn minimum_validator_bond() -> Self::Balance {
		StakingMinBond::get()
	}

	fn desired_validator_count() -> u32 {
		unimplemented!("method currently not used in testing")
	}

	fn current_era() -> EraIndex {
		CurrentEra::get()
	}

	fn bonding_duration() -> EraIndex {
		BondingDuration::get()
	}

	fn status(
		_: &Self::AccountId,
	) -> Result<sp_staking::StakerStatus<Self::AccountId>, DispatchError> {
		Nominations::get()
			.map(|noms| sp_staking::StakerStatus::Nominator(noms))
			.ok_or(DispatchError::Other("NotStash"))
	}

	fn bond_extra(who: &Self::AccountId, extra: Self::Balance) -> DispatchResult {
		let mut x = BondedBalanceMap::get();
		x.get_mut(who).map(|v| *v += extra);
		BondedBalanceMap::set(&x);
		Ok(())
	}

	fn unbond(who: &Self::AccountId, amount: Self::Balance) -> DispatchResult {
		let mut x = BondedBalanceMap::get();
		*x.get_mut(who).unwrap() = x.get_mut(who).unwrap().saturating_sub(amount);
		BondedBalanceMap::set(&x);
		let mut y = UnbondingBalanceMap::get();
		*y.entry(*who).or_insert(Self::Balance::zero()) += amount;
		UnbondingBalanceMap::set(&y);
		Ok(())
	}

	fn chill(_: &Self::AccountId) -> sp_runtime::DispatchResult {
		Ok(())
	}

	fn withdraw_unbonded(who: Self::AccountId, _: u32) -> Result<bool, DispatchError> {
		// Simulates removing unlocking chunks and only having the bonded balance locked
		let mut x = UnbondingBalanceMap::get();
		x.remove(&who);
		UnbondingBalanceMap::set(&x);

		Ok(UnbondingBalanceMap::get().is_empty() && BondedBalanceMap::get().is_empty())
	}

	fn bond(stash: &Self::AccountId, value: Self::Balance, _: &Self::AccountId) -> DispatchResult {
		StakingMock::set_bonded_balance(*stash, value);
		Ok(())
	}

	fn nominate(_: &Self::AccountId, nominations: Vec<Self::AccountId>) -> DispatchResult {
		Nominations::set(&Some(nominations));
		Ok(())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn nominations(_: &Self::AccountId) -> Option<Vec<Self::AccountId>> {
		Nominations::get()
	}

	fn stash_by_ctrl(_controller: &Self::AccountId) -> Result<Self::AccountId, DispatchError> {
		unimplemented!("method currently not used in testing")
	}

	fn stake(who: &Self::AccountId) -> Result<Stake<Balance>, DispatchError> {
		match (
			UnbondingBalanceMap::get().get(who).copied(),
			BondedBalanceMap::get().get(who).copied(),
		) {
			(None, None) => Err(DispatchError::Other("balance not found")),
			(Some(v), None) => Ok(Stake { total: v, active: 0 }),
			(None, Some(v)) => Ok(Stake { total: v, active: v }),
			(Some(a), Some(b)) => Ok(Stake { total: a + b, active: b }),
		}
	}

	fn election_ongoing() -> bool {
		unimplemented!("method currently not used in testing")
	}

	fn force_unstake(_who: Self::AccountId) -> sp_runtime::DispatchResult {
		unimplemented!("method currently not used in testing")
	}

	fn is_exposed_in_era(_who: &Self::AccountId, _era: &EraIndex) -> bool {
		unimplemented!("method currently not used in testing")
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn add_era_stakers(
		_current_era: &EraIndex,
		_stash: &Self::AccountId,
		_exposures: Vec<(Self::AccountId, Self::Balance)>,
	) {
		unimplemented!("method currently not used in testing")
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn set_current_era(_era: EraIndex) {
		unimplemented!("method currently not used in testing")
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
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
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
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
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type Currency = Balances;
	type RewardCounter = RewardCounter;
	type BalanceToU256 = BalanceToU256;
	type U256ToBalance = U256ToBalance;
	type Staking = StakingMock;
	type PostUnbondingPoolsWindow = PostUnbondingPoolsWindow;
	type PalletId = PoolsPalletId;
	type MaxMetadataLen = MaxMetadataLen;
	type MaxUnbonding = MaxUnbonding;
	type MaxPointsToBalance = frame_support::traits::ConstU8<10>;
}

type Block = frame_system::mocking::MockBlock<Runtime>;
frame_support::construct_runtime!(
	pub struct Runtime
	{
		System: frame_system::{Pallet, Call, Storage, Event<T>, Config<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Pools: pools::{Pallet, Call, Storage, Event<T>},
	}
);

pub struct ExtBuilder {
	members: Vec<(AccountId, Balance)>,
	max_members: Option<u32>,
	max_members_per_pool: Option<u32>,
	global_max_commission: Option<Perbill>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			members: Default::default(),
			max_members: Some(4),
			max_members_per_pool: Some(3),
			global_max_commission: Some(Perbill::from_percent(90)),
		}
	}
}

#[cfg_attr(feature = "fuzzing", allow(dead_code))]
impl ExtBuilder {
	// Add members to pool 0.
	pub fn add_members(mut self, members: Vec<(AccountId, Balance)>) -> Self {
		self.members = members;
		self
	}

	pub fn ed(self, ed: Balance) -> Self {
		ExistentialDeposit::set(ed);
		self
	}

	pub fn min_bond(self, min: Balance) -> Self {
		StakingMinBond::set(min);
		self
	}

	pub fn min_join_bond(self, min: Balance) -> Self {
		MinJoinBondConfig::set(min);
		self
	}

	pub fn with_check(self, level: u8) -> Self {
		CheckLevel::set(level);
		self
	}

	pub fn max_members(mut self, max: Option<u32>) -> Self {
		self.max_members = max;
		self
	}

	pub fn max_members_per_pool(mut self, max: Option<u32>) -> Self {
		self.max_members_per_pool = max;
		self
	}

	pub fn global_max_commission(mut self, commission: Option<Perbill>) -> Self {
		self.global_max_commission = commission;
		self
	}

	pub fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let mut storage =
			frame_system::GenesisConfig::<Runtime>::default().build_storage().unwrap();

		let _ = crate::GenesisConfig::<Runtime> {
			min_join_bond: MinJoinBondConfig::get(),
			min_create_bond: 2,
			max_pools: Some(2),
			max_members_per_pool: self.max_members_per_pool,
			max_members: self.max_members,
			global_max_commission: self.global_max_commission,
		}
		.assimilate_storage(&mut storage);

		let mut ext = sp_io::TestExternalities::from(storage);

		ext.execute_with(|| {
			// for events to be deposited.
			frame_system::Pallet::<Runtime>::set_block_number(1);

			// make a pool
			let amount_to_bond = Pools::depositor_min_bond();
			Balances::make_free_balance_be(&10, amount_to_bond * 5);
			assert_ok!(Pools::create(RawOrigin::Signed(10).into(), amount_to_bond, 900, 901, 902));
			assert_ok!(Pools::set_metadata(RuntimeOrigin::signed(900), 1, vec![1, 1]));
			let last_pool = LastPoolId::<Runtime>::get();
			for (account_id, bonded) in self.members {
				Balances::make_free_balance_be(&account_id, bonded * 2);
				assert_ok!(Pools::join(RawOrigin::Signed(account_id).into(), bonded, last_pool));
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce()) {
		self.build().execute_with(|| {
			test();
			Pools::do_try_state(CheckLevel::get()).unwrap();
		})
	}
}

pub fn unsafe_set_state(pool_id: PoolId, state: PoolState) {
	BondedPools::<Runtime>::try_mutate(pool_id, |maybe_bonded_pool| {
		maybe_bonded_pool.as_mut().ok_or(()).map(|bonded_pool| {
			bonded_pool.state = state;
		})
	})
	.unwrap()
}

parameter_types! {
	storage PoolsEvents: u32 = 0;
	storage BalancesEvents: u32 = 0;
}

/// Helper to run a specified amount of blocks.
pub fn run_blocks(n: u64) {
	let current_block = System::block_number();
	run_to_block(n + current_block);
}

/// Helper to run to a specific block.
pub fn run_to_block(n: u64) {
	let current_block = System::block_number();
	assert!(n > current_block);
	while System::block_number() < n {
		Pools::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		Pools::on_initialize(System::block_number());
	}
}

/// All events of this pallet.
pub fn pool_events_since_last_call() -> Vec<super::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::Pools(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = PoolsEvents::get();
	PoolsEvents::set(&(events.len() as u32));
	events.into_iter().skip(already_seen as usize).collect()
}

/// All events of the `Balances` pallet.
pub fn balances_events_since_last_call() -> Vec<pallet_balances::Event<Runtime>> {
	let events = System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::Balances(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>();
	let already_seen = BalancesEvents::get();
	BalancesEvents::set(&(events.len() as u32));
	events.into_iter().skip(already_seen as usize).collect()
}

/// Same as `fully_unbond`, in permissioned setting.
pub fn fully_unbond_permissioned(member: AccountId) -> DispatchResult {
	let points = PoolMembers::<Runtime>::get(member)
		.map(|d| d.active_points())
		.unwrap_or_default();
	Pools::unbond(RuntimeOrigin::signed(member), member, points)
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
