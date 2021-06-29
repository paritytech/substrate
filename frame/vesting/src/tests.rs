use super::*;
use crate as pallet_vesting;

use frame_support::{assert_ok, assert_noop, parameter_types};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, Identity, BadOrigin},
};
use frame_system::RawOrigin;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Vesting: pallet_vesting::{Pallet, Call, Storage, Event<T>, Config<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
parameter_types! {
	pub const MaxLocks: u32 = 10;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type MaxLocks = MaxLocks;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}
parameter_types! {
	pub const MinVestedTransfer: u64 = 256 * 2;
	pub static ExistentialDeposit: u64 = 0;
}
impl Config for Test {
	type Event = Event;
	type Currency = Balances;
	type BlockNumberToBalance = Identity;
	type MinVestedTransfer = MinVestedTransfer;
	type WeightInfo = ();
}

pub struct ExtBuilder {
	existential_deposit: u64,
}
impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			existential_deposit: 1,
		}
	}
}
impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}
	pub fn build(self) -> sp_io::TestExternalities {
		EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10 * self.existential_deposit),
				(2, 20 * self.existential_deposit),
				(3, 30 * self.existential_deposit),
				(4, 40 * self.existential_deposit),
				(12, 10 * self.existential_deposit)
			],
		}.assimilate_storage(&mut t).unwrap();
		pallet_vesting::GenesisConfig::<Test> {
			vesting: vec![
				(1, 0, 10, 5 * self.existential_deposit),
				(2, 10, 20, 0),
				(12, 10, 20, 5 * self.existential_deposit)
			],
		}.assimilate_storage(&mut t).unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

#[test]
fn check_vesting_status() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user1_free_balance = Balances::free_balance(&1);
			let user2_free_balance = Balances::free_balance(&2);
			let user12_free_balance = Balances::free_balance(&12);
			assert_eq!(user1_free_balance, 256 * 10); // Account 1 has free balance
			assert_eq!(user2_free_balance, 256 * 20); // Account 2 has free balance
			assert_eq!(user12_free_balance, 256 * 10); // Account 12 has free balance
			let user1_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 128, // Vesting over 10 blocks
				starting_block: 0,
			};
			let user2_vesting_schedule = VestingInfo {
				locked: 256 * 20,
				per_block: 256, // Vesting over 20 blocks
				starting_block: 10,
			};
			let user12_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_eq!(Vesting::vesting(&1), Some(user1_vesting_schedule)); // Account 1 has a vesting schedule
			assert_eq!(Vesting::vesting(&2), Some(user2_vesting_schedule)); // Account 2 has a vesting schedule
			assert_eq!(Vesting::vesting(&12), Some(user12_vesting_schedule)); // Account 12 has a vesting schedule

			// Account 1 has only 128 units vested from their illiquid 256 * 5 units at block 1
			assert_eq!(Vesting::vesting_balance(&1), Some(128 * 9));
			// Account 2 has their full balance locked
			assert_eq!(Vesting::vesting_balance(&2), Some(user2_free_balance));
			// Account 12 has only their illiquid funds locked
			assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

			System::set_block_number(10);
			assert_eq!(System::block_number(), 10);

			// Account 1 has fully vested by block 10
			assert_eq!(Vesting::vesting_balance(&1), Some(0));
			// Account 2 has started vesting by block 10
			assert_eq!(Vesting::vesting_balance(&2), Some(user2_free_balance));
			// Account 12 has started vesting by block 10
			assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

			System::set_block_number(30);
			assert_eq!(System::block_number(), 30);

			assert_eq!(Vesting::vesting_balance(&1), Some(0)); // Account 1 is still fully vested, and not negative
			assert_eq!(Vesting::vesting_balance(&2), Some(0)); // Account 2 has fully vested by block 30
			assert_eq!(Vesting::vesting_balance(&12), Some(0)); // Account 2 has fully vested by block 30

		});
}

#[test]
fn unvested_balance_should_not_transfer() {
	ExtBuilder::default()
		.existential_deposit(10)
		.build()
		.execute_with(|| {
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 100); // Account 1 has free balance
			// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
			assert_eq!(Vesting::vesting_balance(&1), Some(45));
			assert_noop!(
				Balances::transfer(Some(1).into(), 2, 56),
				pallet_balances::Error::<Test, _>::LiquidityRestrictions,
			); // Account 1 cannot send more than vested amount
		});
}

#[test]
fn vested_balance_should_transfer() {
	ExtBuilder::default()
		.existential_deposit(10)
		.build()
		.execute_with(|| {
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 100); // Account 1 has free balance
			// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
			assert_eq!(Vesting::vesting_balance(&1), Some(45));
			assert_ok!(Vesting::vest(Some(1).into()));
			assert_ok!(Balances::transfer(Some(1).into(), 2, 55));
		});
}

#[test]
fn vested_balance_should_transfer_using_vest_other() {
	ExtBuilder::default()
		.existential_deposit(10)
		.build()
		.execute_with(|| {
			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 100); // Account 1 has free balance
			// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
			assert_eq!(Vesting::vesting_balance(&1), Some(45));
			assert_ok!(Vesting::vest_other(Some(2).into(), 1));
			assert_ok!(Balances::transfer(Some(1).into(), 2, 55));
		});
}

#[test]
fn extra_balance_should_transfer() {
	ExtBuilder::default()
		.existential_deposit(10)
		.build()
		.execute_with(|| {
			assert_ok!(Balances::transfer(Some(3).into(), 1, 100));
			assert_ok!(Balances::transfer(Some(3).into(), 2, 100));

			let user1_free_balance = Balances::free_balance(&1);
			assert_eq!(user1_free_balance, 200); // Account 1 has 100 more free balance than normal

			let user2_free_balance = Balances::free_balance(&2);
			assert_eq!(user2_free_balance, 300); // Account 2 has 100 more free balance than normal

			// Account 1 has only 5 units vested at block 1 (plus 150 unvested)
			assert_eq!(Vesting::vesting_balance(&1), Some(45));
			assert_ok!(Vesting::vest(Some(1).into()));
			assert_ok!(Balances::transfer(Some(1).into(), 3, 155)); // Account 1 can send extra units gained

			// Account 2 has no units vested at block 1, but gained 100
			assert_eq!(Vesting::vesting_balance(&2), Some(200));
			assert_ok!(Vesting::vest(Some(2).into()));
			assert_ok!(Balances::transfer(Some(2).into(), 3, 100)); // Account 2 can send extra units gained
		});
}

#[test]
fn liquid_funds_should_transfer_with_delayed_vesting() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user12_free_balance = Balances::free_balance(&12);

			assert_eq!(user12_free_balance, 2560); // Account 12 has free balance
			// Account 12 has liquid funds
			assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

			// Account 12 has delayed vesting
			let user12_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_eq!(Vesting::vesting(&12), Some(user12_vesting_schedule));

			// Account 12 can still send liquid funds
			assert_ok!(Balances::transfer(Some(12).into(), 3, 256 * 5));
		});
}

#[test]
fn vested_transfer_works() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user3_free_balance = Balances::free_balance(&3);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user3_free_balance, 256 * 30);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 4 should not have any vesting yet.
			assert_eq!(Vesting::vesting(&4), None);
			// Make the schedule for the new transfer.
			let new_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_ok!(Vesting::vested_transfer(Some(3).into(), 4, new_vesting_schedule));
			// Now account 4 should have vesting.
			assert_eq!(Vesting::vesting(&4), Some(new_vesting_schedule));
			// Ensure the transfer happened correctly.
			let user3_free_balance_updated = Balances::free_balance(&3);
			assert_eq!(user3_free_balance_updated, 256 * 25);
			let user4_free_balance_updated = Balances::free_balance(&4);
			assert_eq!(user4_free_balance_updated, 256 * 45);
			// Account 4 has 5 * 256 locked.
			assert_eq!(Vesting::vesting_balance(&4), Some(256 * 5));

			System::set_block_number(20);
			assert_eq!(System::block_number(), 20);

			// Account 4 has 5 * 64 units vested by block 20.
			assert_eq!(Vesting::vesting_balance(&4), Some(10 * 64));

			System::set_block_number(30);
			assert_eq!(System::block_number(), 30);

			// Account 4 has fully vested.
			assert_eq!(Vesting::vesting_balance(&4), Some(0));
		});
}

#[test]
fn vested_transfer_correctly_fails() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user2_free_balance = Balances::free_balance(&2);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user2_free_balance, 256 * 20);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 2 should already have a vesting schedule.
			let user2_vesting_schedule = VestingInfo {
				locked: 256 * 20,
				per_block: 256, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_eq!(Vesting::vesting(&2), Some(user2_vesting_schedule));

			// The vesting schedule we will try to create, fails due to pre-existence of schedule.
			let new_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_noop!(
				Vesting::vested_transfer(Some(4).into(), 2, new_vesting_schedule),
				Error::<Test>::ExistingVestingSchedule,
			);

			// Fails due to too low transfer amount.
			let new_vesting_schedule_too_low = VestingInfo {
				locked: 256 * 1,
				per_block: 64,
				starting_block: 10,
			};
			assert_noop!(
				Vesting::vested_transfer(Some(3).into(), 4, new_vesting_schedule_too_low),
				Error::<Test>::AmountLow,
			);

			// Verify no currency transfer happened.
			assert_eq!(user2_free_balance, 256 * 20);
			assert_eq!(user4_free_balance, 256 * 40);
		});
}

#[test]
fn force_vested_transfer_works() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user3_free_balance = Balances::free_balance(&3);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user3_free_balance, 256 * 30);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 4 should not have any vesting yet.
			assert_eq!(Vesting::vesting(&4), None);
			// Make the schedule for the new transfer.
			let new_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_noop!(Vesting::force_vested_transfer(Some(4).into(), 3, 4, new_vesting_schedule), BadOrigin);
			assert_ok!(Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, new_vesting_schedule));
			// Now account 4 should have vesting.
			assert_eq!(Vesting::vesting(&4), Some(new_vesting_schedule));
			// Ensure the transfer happened correctly.
			let user3_free_balance_updated = Balances::free_balance(&3);
			assert_eq!(user3_free_balance_updated, 256 * 25);
			let user4_free_balance_updated = Balances::free_balance(&4);
			assert_eq!(user4_free_balance_updated, 256 * 45);
			// Account 4 has 5 * 256 locked.
			assert_eq!(Vesting::vesting_balance(&4), Some(256 * 5));

			System::set_block_number(20);
			assert_eq!(System::block_number(), 20);

			// Account 4 has 5 * 64 units vested by block 20.
			assert_eq!(Vesting::vesting_balance(&4), Some(10 * 64));

			System::set_block_number(30);
			assert_eq!(System::block_number(), 30);

			// Account 4 has fully vested.
			assert_eq!(Vesting::vesting_balance(&4), Some(0));
		});
}

#[test]
fn force_vested_transfer_correctly_fails() {
	ExtBuilder::default()
		.existential_deposit(256)
		.build()
		.execute_with(|| {
			let user2_free_balance = Balances::free_balance(&2);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user2_free_balance, 256 * 20);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 2 should already have a vesting schedule.
			let user2_vesting_schedule = VestingInfo {
				locked: 256 * 20,
				per_block: 256, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_eq!(Vesting::vesting(&2), Some(user2_vesting_schedule));

			// The vesting schedule we will try to create, fails due to pre-existence of schedule.
			let new_vesting_schedule = VestingInfo {
				locked: 256 * 5,
				per_block: 64, // Vesting over 20 blocks
				starting_block: 10,
			};
			assert_noop!(
				Vesting::force_vested_transfer(RawOrigin::Root.into(), 4, 2, new_vesting_schedule),
				Error::<Test>::ExistingVestingSchedule,
			);

			// Fails due to too low transfer amount.
			let new_vesting_schedule_too_low = VestingInfo {
				locked: 256 * 1,
				per_block: 64,
				starting_block: 10,
			};
			assert_noop!(
				Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, new_vesting_schedule_too_low),
				Error::<Test>::AmountLow,
			);

			// Verify no currency transfer happened.
			assert_eq!(user2_free_balance, 256 * 20);
			assert_eq!(user4_free_balance, 256 * 40);
		});
}
