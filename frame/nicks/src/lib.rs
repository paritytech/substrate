// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
//! - [`Config`] - Pallet configuration
//! - [`Call`]  - Callable functions _(dispatchable extrinsics)_ available in this pallet
//! - [`Event`] - Events emitted by this pallet
//! - [`Error`] - Possible errors which may be returned by the dispatchable extrinsics
//!
//! ## Overview
//!
//! The `pallet_nicks` is an _example_ pallet for keeping track of account names on-chain.
//! It makes no effort to create a name hierarchy, be a DNS replacement or provide reverse lookups.
//! 
//! <div class="example-wrap" style="display:inline-block"><pre class="compile_fail"
//! style="white-space:normal;font:inherit;">
//! <strong>WARNING</strong>:
//! The weights attached to this pallet's dispatchable functions are for demonstration purposes only and
//! have not been designed to be economically secure. <strong style="color:red">Do not use this pallet as-is in production.</strong>
//! </pre></div>
//!
//! ### Dispatchable Functions
//!
//! * [`set_name`](Pallet::set_name) - Set the associated name of an account; a small deposit is reserved if not already
//!   taken.
//! * [`clear_name`](Pallet::clear_name) - Remove an account's associated name; the deposit is returned.
//! * [`kill_name`](Pallet::kill_name) - Forcibly remove the associated name; the deposit is lost.

#![deny(missing_docs)]
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
		/// As this pallet can emit [events](Event) it depends on the runtime's definition of an event
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// [`ReservableCurrency`](frame_support::traits::ReservableCurrency),
		/// used to reserve the [`ReservationFee`](Self::ReservationFee) from the caller's balance
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Amount reserved from caller's balance when a name is set via [`set_name`](Pallet::set_name).
		/// Fee can be unreserved via [`clear_name`](Pallet::clear_name)
		/// 
		/// **NB:** It is possible to lose this fee to [slashing](Pallet::kill_name)
		#[pallet::constant]
		type ReservationFee: Get<BalanceOf<Self>>;

		/// What to do with reserved balance if slashed via [`kill_name`](Pallet::kill_name)
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The origin which may forcibly [set](Pallet::set_name) or [remove](Pallet::kill_name) a name.
		/// **Root can always do this.**
		type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The minimum length in bytes that a name can be
		#[pallet::constant]
		type MinLength: Get<u32>;

		/// The maximum length in bytes that a name can be
		/// 
		/// **NB:** Any storage item whose size is determined by user action should have a bound on it
		#[pallet::constant]
		type MaxLength: Get<u32>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A name was [set](Pallet::set_name)
		NameSet {
			/// The account for which a name was set and who paid the `ReservationFee`
			who: T::AccountId,
		},
		/// A name was [forcibly set](Pallet::force_name)
		NameForced {
			/// The account whose name was forcibly set and which potentially paid the `ReservationFee`
			target: T::AccountId,
		},
		/// An existing name was [changed](Pallet::set_name)
		NameChanged {
			/// The account associated with the name which was changed
			who: T::AccountId,
		},
		/// A name was [cleared](Pallet::clear_name), and the `ReservationFee` was returned
		NameCleared {
			/// The account associated with the name which was cleared
			who: T::AccountId,
			/// The amount of reserved currency which was returned
			deposit: BalanceOf<T>,
		},
		/// A name was [removed](Pallet::kill_name) and the `ReservationFee` slashed
		NameKilled {
			/// The account associated with the name which was removed
			target: T::AccountId,
			/// The amount of reserved currency which was slashed
			deposit: BalanceOf<T>,
		},
	}

	/// Possible errors which can be returned by the nicks pallet [dispatchable functions](Call)
	#[pallet::error]
	pub enum Error<T> {
		/// The supplied name is shorter than the `MinLength` specified in the pallet [`Config`]
		TooShort,
		/// The supplied name is longer than the `MaxLength` specified in the pallet [`Config`]
		TooLong,
		/// Attempting to remove a name for an account which does not have a name set
		Unnamed,
	}

	/// Names are stored as a bytes array alongside the amount of balance reserved as a fee.
	/// It is safe to use the [Twox64Concat](frame_support::Twox64Concat) hasher
	/// as the key preimage (`AccountId`) is a secure hash
	#[pallet::storage]
	pub(super) type NameOf<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, (BoundedVec<u8, T::MaxLength>, BalanceOf<T>)>;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set an account's name. The name should be a UTF-8-encoded string by convention, though
		/// we don't check it.
		///
		/// The name may not be more than [`MaxLength`](Config::MaxLength) bytes,
		/// or less than [`MinLength`](Config::MinLength) bytes.
		///
		/// If the account doesn't already have a name, then a fee of [`ReservationFee`](Config::ReservationFee)
		/// is reserved in the account.
		///
		/// The dispatch origin for this call must be _Signed_.
		/// 
		/// # Errors
		/// 
		/// If the size of the supplied name is not within the bounds defined in [`Config`]
		/// the function returns an [`Error::TooShort`] or [`Error::TooLong`]
		/// 
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(0)]
		#[pallet::weight({50_000_000})]
		pub fn set_name(origin: OriginFor<T>, name: Vec<u8>) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let bounded_name: BoundedVec<_, _> =
				name.try_into().map_err(|_| Error::<T>::TooLong)?;
			ensure!(bounded_name.len() >= T::MinLength::get() as usize, Error::<T>::TooShort);

			// if a name already exists in storage we do not reserve any additional fee
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

		/// Clear an account's name and return the [deposit](Config::ReservationFee).
		/// Fails if the account was not named.
		///
		/// The dispatch origin for this call must be _Signed_.
		/// 
		/// # Errors
		/// 
		/// If no name exists in storage for the account this function returns an [`Error::Unnamed`]
		/// 
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(1)]
		#[pallet::weight({70_000_000})]
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
		/// Fails if `target` has not been named. The deposit is dealt with via the [`Slashed`](Config::Slashed)
		/// imbalance handler.
		///
		/// The dispatch origin for this call must match [`ForceOrigin`](Config::ForceOrigin).
		/// 
		/// # Errors
		/// 
		/// If no name exists in storage for the account this function returns an [`Error::Unnamed`]
		/// 
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(2)]
		#[pallet::weight({70_000_000})]
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

		/// Forcibly set a third-party account's name. 
		/// 
		/// No [deposit](Config::ReservationFee) is taken for the name,
		/// however if a name already exists for the account any existing deposit is retained
		///
		/// The name size can not exceed the [`MaxLength`](Config::MaxLength), but no
		/// other length checks are performed.
		///
		/// The dispatch origin for this call must match [`ForceOrigin`](Config::ForceOrigin).
		/// 
		/// # Errors
		/// 
		/// If the size of the supplied name exceeds the [`MaxLength`](Config::MaxLength) value
		/// from the [`Config`] this function returns an [`Error::TooLong`]
		/// 
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(3)]
		#[pallet::weight({70_000_000})]
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
		traits::{BadOrigin, BlakeTwo256, IdentityLookup},
		BuildStorage,
	};

	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test
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
		type Nonce = u64;
		type Hash = H256;
		type RuntimeCall = RuntimeCall;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Block = Block;
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
		type FreezeIdentifier = ();
		type MaxFreezes = ();
		type RuntimeHoldReason = ();
		type MaxHolds = ();
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
		let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
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
