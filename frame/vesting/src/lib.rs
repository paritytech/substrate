// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Vesting Module
//!
//! - [`vesting::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! A simple module providing a means of placing a linear curve on an account's locked balance. This
//! module ensures that there is a lock in place preventing the balance to drop below the *unvested*
//! amount for any reason other than transaction fee payment.
//!
//! As the amount vested increases over time, the amount unvested reduces. However, locks remain in
//! place and explicit action is needed on behalf of the user to ensure that the amount locked is
//! equivalent to the amount remaining to be vested. This is done through a dispatchable function,
//! either `vest` (in typical case where the sender is calling on their own behalf) or `vest_other`
//! in case the sender is calling on another account's behalf.
//!
//! ## Interface
//!
//! This module implements the `VestingSchedule` trait.
//!
//! ### Dispatchable Functions
//!
//! - `vest` - Update the lock, reducing it in line with the amount "vested" so far.
//! - `vest_other` - Update the lock of another account, reducing it in line with the amount
//!   "vested" so far.
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_std::fmt::Debug;
use codec::{Encode, Decode};
use sp_runtime::{DispatchResult, RuntimeDebug, traits::{
	StaticLookup, Zero, AtLeast32Bit, MaybeSerializeDeserialize, Convert
}};
use frame_support::{decl_module, decl_event, decl_storage, decl_error};
use frame_support::traits::{
	Currency, LockableCurrency, VestingSchedule, WithdrawReason, LockIdentifier
};
use frame_system::{self as system, ensure_signed};

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The currency trait.
	type Currency: LockableCurrency<Self::AccountId>;

	/// Convert the block number into a balance.
	type BlockNumberToBalance: Convert<Self::BlockNumber, BalanceOf<Self>>;
}

const VESTING_ID: LockIdentifier = *b"vesting ";

/// Struct to encode the vesting schedule of an individual account.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct VestingInfo<Balance, BlockNumber> {
	/// Locked amount at genesis.
	pub locked: Balance,
	/// Amount that gets unlocked every block after `starting_block`.
	pub per_block: Balance,
	/// Starting block for unlocking(vesting).
	pub starting_block: BlockNumber,
}

impl<
	Balance: AtLeast32Bit + Copy,
	BlockNumber: AtLeast32Bit + Copy,
> VestingInfo<Balance, BlockNumber> {
	/// Amount locked at block `n`.
	pub fn locked_at<
		BlockNumberToBalance: Convert<BlockNumber, Balance>
	>(&self, n: BlockNumber) -> Balance {
		// Number of blocks that count toward vesting
		// Saturating to 0 when n < starting_block
		let vested_block_count = n.saturating_sub(self.starting_block);
		let vested_block_count = BlockNumberToBalance::convert(vested_block_count);
		// Return amount that is still locked in vesting
		let maybe_balance = vested_block_count.checked_mul(&self.per_block);
		if let Some(balance) = maybe_balance {
			self.locked.saturating_sub(balance)
		} else {
			Zero::zero()
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Vesting {
		/// Information regarding the vesting of a given account.
		pub Vesting get(fn vesting):
			map hasher(blake2_256) T::AccountId => Option<VestingInfo<BalanceOf<T>, T::BlockNumber>>;
	}
	add_extra_genesis {
		config(vesting): Vec<(T::AccountId, T::BlockNumber, T::BlockNumber, BalanceOf<T>)>;
		build(|config: &GenesisConfig<T>| {
			use sp_runtime::traits::Saturating;
			// Generate initial vesting configuration
			// * who - Account which we are generating vesting configuration for
			// * begin - Block when the account will start to vest
			// * length - Number of blocks from `begin` until fully vested
			// * liquid - Number of units which can be spent before vesting begins
			for &(ref who, begin, length, liquid) in config.vesting.iter() {
				let balance = T::Currency::free_balance(who);
				assert!(!balance.is_zero(), "Currencies must be init'd before vesting");
				// Total genesis `balance` minus `liquid` equals funds locked for vesting
				let locked = balance.saturating_sub(liquid);
				let length_as_balance = T::BlockNumberToBalance::convert(length);
				let per_block = locked / length_as_balance.max(sp_runtime::traits::One::one());

				Vesting::<T>::insert(who, VestingInfo {
					locked: locked,
					per_block: per_block,
					starting_block: begin
				});
				let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
				T::Currency::set_lock(VESTING_ID, who, locked, reasons);
			}
		})
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId, Balance = BalanceOf<T> {
		/// The amount vested has been updated. This could indicate more funds are available. The
		/// balance given is the amount which is left unvested (and thus locked).
		VestingUpdated(AccountId, Balance),
		/// An account (given) has become fully vested. No further vesting can happen.
		VestingCompleted(AccountId),
	}
);

decl_error! {
	/// Error for the vesting module.
	pub enum Error for Module<T: Trait> {
		/// The account given is not vesting.
		NotVesting,
		/// An existing vesting schedule already exists for this account that cannot be clobbered.
		ExistingVestingSchedule,
	}
}

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what it's working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Unlock any vested funds of the sender account.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have funds still
		/// locked under this module.
		///
		/// Emits either `VestingCompleted` or `VestingUpdated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One balance-lock operation.
		/// - One storage read (codec `O(1)`) and up to one removal.
		/// - One event.
		/// # </weight>
		fn vest(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::update_lock(who)
		}

		/// Unlock any vested funds of a `target` account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `target`: The account whose vested funds should be unlocked. Must have funds still
		/// locked under this module.
		///
		/// Emits either `VestingCompleted` or `VestingUpdated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - Up to one account lookup.
		/// - One balance-lock operation.
		/// - One storage read (codec `O(1)`) and up to one removal.
		/// - One event.
		/// # </weight>
		fn vest_other(origin, target: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
			ensure_signed(origin)?;
			Self::update_lock(T::Lookup::lookup(target)?)
		}
	}
}

impl<T: Trait> Module<T> {
	/// (Re)set or remove the module's currency lock on `who`'s account in accordance with their
	/// current unvested amount.
	fn update_lock(who: T::AccountId) -> DispatchResult {
		let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;
		let now = <frame_system::Module<T>>::block_number();
		let locked_now = vesting.locked_at::<T::BlockNumberToBalance>(now);

		if locked_now.is_zero() {
			T::Currency::remove_lock(VESTING_ID, &who);
			Vesting::<T>::remove(&who);
			Self::deposit_event(RawEvent::VestingCompleted(who));
		} else {
			let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
			T::Currency::set_lock(VESTING_ID, &who, locked_now, reasons);
			Self::deposit_event(RawEvent::VestingUpdated(who, locked_now));
		}
		Ok(())
	}
}

impl<T: Trait> VestingSchedule<T::AccountId> for Module<T> where
	BalanceOf<T>: MaybeSerializeDeserialize + Debug
{
	type Moment = T::BlockNumber;
	type Currency = T::Currency;

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	fn vesting_balance(who: &T::AccountId) -> Option<BalanceOf<T>> {
		if let Some(v) = Self::vesting(who) {
			let now = <frame_system::Module<T>>::block_number();
			let locked_now = v.locked_at::<T::BlockNumberToBalance>(now);
			Some(T::Currency::free_balance(who).min(locked_now))
		} else {
			None
		}
	}

	/// Adds a vesting schedule to a given account.
	///
	/// If there already exists a vesting schedule for the given account, an `Err` is returned
	/// and nothing is updated.
	///
	/// On success, a linearly reducing amount of funds will be locked. In order to realise any
	/// reduction of the lock over time as it diminishes, the account owner must use `vest` or
	/// `vest_other`.
	///
	/// Is a no-op if the amount to be vested is zero.
	fn add_vesting_schedule(
		who: &T::AccountId,
		locked: BalanceOf<T>,
		per_block: BalanceOf<T>,
		starting_block: T::BlockNumber
	) -> DispatchResult {
		if locked.is_zero() { return Ok(()) }
		if Vesting::<T>::contains_key(who) {
			Err(Error::<T>::ExistingVestingSchedule)?
		}
		let vesting_schedule = VestingInfo {
			locked,
			per_block,
			starting_block
		};
		Vesting::<T>::insert(who, vesting_schedule);
		// it can't fail, but even if somehow it did, we don't really care.
		let _ = Self::update_lock(who.clone());
		Ok(())
	}

	/// Remove a vesting schedule for a given account.
	fn remove_vesting_schedule(who: &T::AccountId) {
		Vesting::<T>::remove(who);
		// it can't fail, but even if somehow it did, we don't really care.
		let _ = Self::update_lock(who.clone());
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::cell::RefCell;
	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, weights::Weight,
		traits::Get
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup, Identity, OnInitialize},
	};
	use sp_storage::Storage;

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	// For testing the pallet, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of pallets we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type DustRemoval = ();
		type Event = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	impl Trait for Test {
		type Event = ();
		type Currency = Balances;
		type BlockNumberToBalance = Identity;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Vesting = Module<Test>;

	thread_local! {
		static EXISTENTIAL_DEPOSIT: RefCell<u64> = RefCell::new(0);
	}
	pub struct ExistentialDeposit;
	impl Get<u64> for ExistentialDeposit {
		fn get() -> u64 { EXISTENTIAL_DEPOSIT.with(|v| *v.borrow()) }
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
			GenesisConfig::<Test> {
				vesting: vec![
					(1, 0, 10, 5 * self.existential_deposit),
					(2, 10, 20, 0),
					(12, 10, 20, 5 * self.existential_deposit)
				],
			}.assimilate_storage(&mut t).unwrap();
			t.into()
		}
	}

	#[test]
	fn vesting_info_via_migration_should_work() {
		let mut s = Storage::default();
		use hex_literal::hex;
		// A dump of data from the previous version for which we know account 6 vests 30 of its 60
		// over 5  blocks from block 3.
		let data = vec![
			(hex!["26aa394eea5630e07c48ae0c9558cef702a5c1b19ab7a04f536c519aca4983ac"].to_vec(), hex!["0100000000000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef70a98fdbe9ce6c55837576c60c7af3850"].to_vec(), hex!["02000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7"].to_vec(), hex!["08000000000000000000000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef78a42f33323cb5ced3b44dd825fda9fcc"].to_vec(), hex!["4545454545454545454545454545454545454545454545454545454545454545"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef7a44704b568d21667356a5a050c11874681e47a19e6b29b0a65b9591762ce5143ed30d0261e5d24a3201752506b20f15c"].to_vec(), hex!["4545454545454545454545454545454545454545454545454545454545454545"].to_vec()),
			(hex!["3a636f6465"].to_vec(), hex![""].to_vec()),
			(hex!["3a65787472696e7369635f696e646578"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["3a686561707061676573"].to_vec(), hex!["0800000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc61dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["046d697363202020200300000000000000ffffffffffffffff04"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc66cddb367afbd583bb48f9bbd7d5ba3b1d0738b4881b1cddd38169526d8158137"].to_vec(), hex!["0474786665657320200300000000000000ffffffffffffffff01"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc6e88b43fded6323ef02ffeffbd8c40846ee09bf316271bd22369659c959dd733a"].to_vec(), hex!["08616c6c20202020200300000000000000ffffffffffffffff1f64656d6f63726163ffffffffffffffff030000000000000002"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f3c22813def93ef32c365b55cb92f10f91dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["0500000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80"].to_vec(), hex!["d200000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f5f27b51b5ec208ee9cb25b55d8728243b8788bb218b185b63e3e92653953f29b6b143fb8cf5159fc908632e6fe490501"].to_vec(), hex!["1e0000000000000006000000000000000200000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b41dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["0500000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b46cddb367afbd583bb48f9bbd7d5ba3b1d0738b4881b1cddd38169526d8158137"].to_vec(), hex!["1e00000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4b8788bb218b185b63e3e92653953f29b6b143fb8cf5159fc908632e6fe490501"].to_vec(), hex!["3c00000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4e88b43fded6323ef02ffeffbd8c40846ee09bf316271bd22369659c959dd733a"].to_vec(), hex!["1400000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4e96760d274653a39b429a87ebaae9d3aa4fdf58b9096cf0bebc7c4e5a4c2ed8d"].to_vec(), hex!["2800000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4effb728943197fd12e694cbf3f3ede28fbf7498b0370c6dfa0013874b417c178"].to_vec(), hex!["3200000000000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911b7f17cdfbfa73331856cca0acddd7842e"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911bbdcb0c5143a8617ed38ae3810dd45bc6"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911be2f6cb0456905c189bcb0458f9440f13"].to_vec(), hex!["00000000"].to_vec()),
		];
		s.top = data.into_iter().collect();
		sp_io::TestExternalities::new(s).execute_with(|| {
			Balances::on_initialize(1);
			assert_eq!(Balances::free_balance(6), 60);
			assert_eq!(Balances::usable_balance(&6), 30);
			System::set_block_number(2);
			assert_ok!(Vesting::vest(Origin::signed(6)));
			assert_eq!(Balances::usable_balance(&6), 30);
			System::set_block_number(3);
			assert_ok!(Vesting::vest(Origin::signed(6)));
			assert_eq!(Balances::usable_balance(&6), 36);
			System::set_block_number(4);
			assert_ok!(Vesting::vest(Origin::signed(6)));
			assert_eq!(Balances::usable_balance(&6), 42);
		});
	}

	#[test]
	fn check_vesting_status() {
		ExtBuilder::default()
			.existential_deposit(256)
			.build()
			.execute_with(|| {
				assert_eq!(System::block_number(), 1);
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
				assert_eq!(System::block_number(), 1);
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
				assert_eq!(System::block_number(), 1);
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
				assert_eq!(System::block_number(), 1);
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
				assert_eq!(System::block_number(), 1);
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
				assert_eq!(System::block_number(), 1);
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
}
