// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Nicks Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! Nicks is an example pallet for keeping track of account names on-chain. It makes no effort to
//! create a name hierarchy, be a DNS replacement or provide reverse lookups. Furthermore, the
//! weights attached to this pallet's dispatchable functions are for demonstration purposes only and
//! have not been designed to be economically secure. Do not use this pallet as-is in production.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set_name` - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! * `clear_name` - Remove an account's associated name; the deposit is returned.
//! * `kill_name` - Forcibly remove the associated name; the deposit is lost.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::{Currency, OnUnbalanced, ReservableCurrency};
pub use pallet::*;
use sp_runtime::traits::{StaticLookup, Zero};
use sp_std::prelude::*;

type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
type BalanceOf<T> = <<T as Config>::Currency as Currency<AccountIdOf<T>>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as Config>::Currency as Currency<AccountIdOf<T>>>::NegativeImbalance;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The currency trait.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Reservation fee.
		#[pallet::constant]
		type ReservationFee: Get<BalanceOf<Self>>;

		/// What to do with slashed funds.
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The origin which may forcibly set or remove a name. Root can always do this.
		type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The minimum length a name may be.
		#[pallet::constant]
		type MinLength: Get<u32>;

		/// The maximum length a name may be.
		#[pallet::constant]
		type MaxLength: Get<u32>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A name was set.
		NameSet { who: T::AccountId },
		/// A name was forcibly set.
		NameForced { target: T::AccountId },
		/// A name was changed.
		NameChanged { who: T::AccountId },
		/// A name was cleared, and the given balance returned.
		NameCleared { who: T::AccountId, deposit: BalanceOf<T> },
		/// A name was removed and the given balance slashed.
		NameKilled { target: T::AccountId, deposit: BalanceOf<T> },
	}

	/// Error for the nicks pallet.
	#[pallet::error]
	pub enum Error<T> {
		/// A name is too short.
		TooShort,
		/// A name is too long.
		TooLong,
		/// An account isn't named.
		Unnamed,
	}

	/// The lookup table for names.
	#[pallet::storage]
	pub(super) type NameOf<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, (BoundedVec<u8, T::MaxLength>, BalanceOf<T>)>;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set an account's name. The name should be a UTF-8-encoded string by convention, though
		/// we don't check it.
		///
		/// The name may not be more than `T::MaxLength` bytes, nor less than `T::MinLength` bytes.
		///
		/// If the account doesn't already have a name, then a fee of `ReservationFee` is reserved
		/// in the account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(0)]
		#[pallet::weight(50_000_000)]
		pub fn set_name(origin: OriginFor<T>, name: Vec<u8>) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let bounded_name: BoundedVec<_, _> =
				name.try_into().map_err(|_| Error::<T>::TooLong)?;
			ensure!(bounded_name.len() >= T::MinLength::get() as usize, Error::<T>::TooShort);

			let deposit = if let Some((_, deposit)) = <NameOf<T>>::get(&sender) {
				Self::deposit_event(Event::<T>::NameChanged { who: sender.clone() });
				deposit
			} else {
				let deposit = T::ReservationFee::get();
				T::Currency::reserve(&sender, deposit)?;
				Self::deposit_event(Event::<T>::NameSet { who: sender.clone() });
				deposit
			};

			<NameOf<T>>::insert(&sender, (bounded_name, deposit));
			Ok(())
		}

		/// Clear an account's name and return the deposit. Fails if the account was not named.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(1)]
		#[pallet::weight(70_000_000)]
		pub fn clear_name(origin: OriginFor<T>) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let deposit = <NameOf<T>>::take(&sender).ok_or(Error::<T>::Unnamed)?.1;

			let err_amount = T::Currency::unreserve(&sender, deposit);
			debug_assert!(err_amount.is_zero());

			Self::deposit_event(Event::<T>::NameCleared { who: sender, deposit });
			Ok(())
		}

		/// Remove an account's name and take charge of the deposit.
		///
		/// Fails if `target` has not been named. The deposit is dealt with through `T::Slashed`
		/// imbalance handler.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(2)]
		#[pallet::weight(70_000_000)]
		pub fn kill_name(origin: OriginFor<T>, target: AccountIdLookupOf<T>) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let deposit = <NameOf<T>>::take(&target).ok_or(Error::<T>::Unnamed)?.1;
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit).0);

			Self::deposit_event(Event::<T>::NameKilled { target, deposit });
			Ok(())
		}

		/// Set a third-party account's name with no deposit.
		///
		/// No length checking is done on the name.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(3)]
		#[pallet::weight(70_000_000)]
		pub fn force_name(
			origin: OriginFor<T>,
			target: AccountIdLookupOf<T>,
			name: Vec<u8>,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			let bounded_name: BoundedVec<_, _> =
				name.try_into().map_err(|_| Error::<T>::TooLong)?;
			let target = T::Lookup::lookup(target)?;
			let deposit = <NameOf<T>>::get(&target).map(|x| x.1).unwrap_or_else(Zero::zero);
			<NameOf<T>>::insert(&target, (bounded_name, deposit));

			Self::deposit_event(Event::<T>::NameForced { target });
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_nicks;

	use frame_support::{
		assert_noop, assert_ok, ord_parameter_types,
		traits::{ConstU32, ConstU64},
	};
	use frame_system::EnsureSignedBy;
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system,
			Balances: pallet_balances,
			Nicks: pallet_nicks,
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type RuntimeOrigin = RuntimeOrigin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type RuntimeCall = RuntimeCall;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type RuntimeEvent = RuntimeEvent;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type Balance = u64;
		type RuntimeEvent = RuntimeEvent;
		type DustRemoval = ();
		type ExistentialDeposit = ConstU64<1>;
		type AccountStore = System;
		type WeightInfo = ();
	}

	ord_parameter_types! {
		pub const One: u64 = 1;
	}
	impl Config for Test {
		type RuntimeEvent = RuntimeEvent;
		type Currency = Balances;
		type ReservationFee = ConstU64<2>;
		type Slashed = ();
		type ForceOrigin = EnsureSignedBy<One, u64>;
		type MinLength = ConstU32<3>;
		type MaxLength = ConstU32<16>;
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> { balances: vec![(1, 10), (2, 10)] }
			.assimilate_storage(&mut t)
			.unwrap();
		t.into()
	}

	#[test]
	fn kill_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(RuntimeOrigin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::total_balance(&2), 10);
			assert_ok!(Nicks::kill_name(RuntimeOrigin::signed(1), 2));
			assert_eq!(Balances::total_balance(&2), 8);
			assert_eq!(<NameOf<Test>>::get(2), None);
		});
	}

	#[test]
	fn force_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Nicks::set_name(RuntimeOrigin::signed(2), b"Dr. David Brubeck, III".to_vec()),
				Error::<Test>::TooLong,
			);

			assert_ok!(Nicks::set_name(RuntimeOrigin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::reserved_balance(2), 2);
			assert_noop!(
				Nicks::force_name(RuntimeOrigin::signed(1), 2, b"Dr. David Brubeck, III".to_vec()),
				Error::<Test>::TooLong,
			);
			assert_ok!(Nicks::force_name(
				RuntimeOrigin::signed(1),
				2,
				b"Dr. Brubeck, III".to_vec()
			));
			assert_eq!(Balances::reserved_balance(2), 2);
			let (name, amount) = <NameOf<Test>>::get(2).unwrap();
			assert_eq!(name, b"Dr. Brubeck, III".to_vec());
			assert_eq!(amount, 2);
		});
	}

	#[test]
	fn normal_operation_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Nicks::set_name(RuntimeOrigin::signed(1), b"Gav".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gav".to_vec());

			assert_ok!(Nicks::set_name(RuntimeOrigin::signed(1), b"Gavin".to_vec()));
			assert_eq!(Balances::reserved_balance(1), 2);
			assert_eq!(Balances::free_balance(1), 8);
			assert_eq!(<NameOf<Test>>::get(1).unwrap().0, b"Gavin".to_vec());

			assert_ok!(Nicks::clear_name(RuntimeOrigin::signed(1)));
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(1), 10);
		});
	}

	#[test]
	fn error_catching_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(Nicks::clear_name(RuntimeOrigin::signed(1)), Error::<Test>::Unnamed);

			assert_noop!(
				Nicks::set_name(RuntimeOrigin::signed(3), b"Dave".to_vec()),
				pallet_balances::Error::<Test, _>::InsufficientBalance
			);

			assert_noop!(
				Nicks::set_name(RuntimeOrigin::signed(1), b"Ga".to_vec()),
				Error::<Test>::TooShort
			);
			assert_noop!(
				Nicks::set_name(RuntimeOrigin::signed(1), b"Gavin James Wood, Esquire".to_vec()),
				Error::<Test>::TooLong
			);
			assert_ok!(Nicks::set_name(RuntimeOrigin::signed(1), b"Dave".to_vec()));
			assert_noop!(Nicks::kill_name(RuntimeOrigin::signed(2), 1), BadOrigin);
			assert_noop!(
				Nicks::force_name(RuntimeOrigin::signed(2), 1, b"Whatever".to_vec()),
				BadOrigin
			);
		});
	}
}
