// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! # Assets Module
//!
//! A simple, secure module for dealing with fungible assets.
//!
//! ## Overview
//!
//! The Assets module provides functionality for asset management of fungible asset classes
//! with a fixed supply, including:
//!
//! * Asset Issuance
//! * Asset Transfer
//! * Asset Destruction
//!
//! To use it in your runtime, you need to implement the assets [`Trait`](./trait.Trait.html).
//!
//! The supported dispatchable functions are documented in the [`Call`](./enum.Call.html) enum.
//!
//! ### Terminology
//!
//! * **Asset issuance:** The creation of a new asset, whose total supply will belong to the
//!   account that issues the asset.
//! * **Asset transfer:** The action of transferring assets from one account to another.
//! * **Asset destruction:** The process of an account removing its entire holding of an asset.
//! * **Fungible asset:** An asset whose units are interchangeable.
//! * **Non-fungible asset:** An asset for which each unit has unique characteristics.
//!
//! ### Goals
//!
//! The assets system in Substrate is designed to make the following possible:
//!
//! * Issue a unique asset to its creator's account.
//! * Move assets between accounts.
//! * Remove an account's balance of an asset when requested by that account's owner and update
//!   the asset's total supply.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `issue` - Issues the total supply of a new fungible asset to the account of the caller of the function.
//! * `transfer` - Transfers an `amount` of units of fungible asset `id` from the balance of
//! the function caller's account (`origin`) to a `target` account.
//! * `destroy` - Destroys the entire holding of a fungible asset `id` associated with the account
//! that called the function.
//!
//! Please refer to the [`Call`](./enum.Call.html) enum and its associated variants for documentation on each function.
//!
//! ### Public Functions
//! <!-- Original author of descriptions: @gavofyork -->
//!
//! * `balance` - Get the asset `id` balance of `who`.
//! * `total_supply` - Get the total supply of an asset `id`.
//!
//! Please refer to the [`Module`](./struct.Module.html) struct for details on publicly available functions.
//!
//! ## Usage
//!
//! The following example shows how to use the Assets module in your runtime by exposing public functions to:
//!
//! * Issue a new fungible asset for a token distribution event (airdrop).
//! * Query the fungible asset holding balance of an account.
//! * Query the total supply of a fungible asset that has been issued.
//!
//! ### Prerequisites
//!
//! Import the Assets module and types and derive your runtime's configuration traits from the Assets module trait.
//!
//! ### Simple Code Snippet
//!
//! ```rust,ignore
//! use pallet_assets as assets;
//! use frame_support::{decl_module, dispatch, ensure};
//! use frame_system::ensure_signed;
//!
//! pub trait Trait: assets::Trait { }
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn issue_token_airdrop(origin) -> dispatch::DispatchResult {
//! 			let sender = ensure_signed(origin).map_err(|e| e.as_str())?;
//!
//! 			const ACCOUNT_ALICE: u64 = 1;
//! 			const ACCOUNT_BOB: u64 = 2;
//! 			const COUNT_AIRDROP_RECIPIENTS: u64 = 2;
//! 			const TOKENS_FIXED_SUPPLY: u64 = 100;
//!
//! 			ensure!(!COUNT_AIRDROP_RECIPIENTS.is_zero(), "Divide by zero error.");
//!
//! 			let asset_id = Self::next_asset_id();
//!
//! 			NextAssetId::<T>::mutate(|asset_id| *asset_id += 1);
//! 			Balances::<T>::insert((asset_id, &ACCOUNT_ALICE), TOKENS_FIXED_SUPPLY / COUNT_AIRDROP_RECIPIENTS);
//! 			Balances::<T>::insert((asset_id, &ACCOUNT_BOB), TOKENS_FIXED_SUPPLY / COUNT_AIRDROP_RECIPIENTS);
//! 			TotalSupply::<T>::insert(asset_id, TOKENS_FIXED_SUPPLY);
//!
//! 			Self::deposit_event(RawEvent::Issued(asset_id, sender, TOKENS_FIXED_SUPPLY));
//! 			Ok(())
//! 		}
//! 	}
//! }
//! ```
//!
//! ## Assumptions
//!
//! Below are assumptions that must be held when using this module.  If any of
//! them are violated, the behavior of this module is undefined.
//!
//! * The total count of assets should be less than
//!   `Trait::AssetId::max_value()`.
//!
//! ## Related Modules
//!
//! * [`System`](../frame_system/index.html)
//! * [`Support`](../frame_support/index.html)

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{fmt::Debug};
use sp_runtime::{RuntimeDebug, traits::{
	Member, AtLeast32Bit, AtLeast32BitUnsigned, Zero, StaticLookup, One, Saturating, CheckedSub
}};
use codec::{Encode, Decode};
use frame_support::{Parameter, decl_module, decl_event, decl_storage, decl_error, ensure,
	traits::{Currency, ReservableCurrency}, dispatch::DispatchResult,
};
use frame_system::ensure_signed;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// The module configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The units in which we record balances.
	type Balance: Member + Parameter + AtLeast32BitUnsigned + Default + Copy;

	/// The arithmetic type of asset identifier.
	type AssetId: Parameter + AtLeast32Bit + Default + Copy;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct AssetDetails<
	Balance: Encode + Decode + Clone + Debug + Eq + PartialEq,
	AccountId: Encode + Decode + Clone + Debug + Eq + PartialEq,
	DepositBalance: Encode + Decode + Clone + Debug + Eq + PartialEq,
> {
	/// Can change `owner`, `issuer`, `freezer` and `admin` accounts.
	owner: AccountId,
	/// Can mint tokens.
	issuer: AccountId,
	/// Can thaw tokens, force transfers and burn tokens from any account.
	admin: AccountId,
	/// Can freeze tokens.
	freezer: AccountId,
	/// The total supply across all accounts.
	supply: Balance,
	/// The balance deposited for this asset; this pays for the data stored here together with any
	/// virtual accounts.
	deposit: DepositBalance,
	/// The number of balance-holding accounts that this asset may have, excluding those that were
	/// created when they had a system-level ED.
	max_zombies: u32,
	/// The ED for virtual accounts.
	minimum_balance: Balance,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default)]
pub struct AccountData<
	Balance: Encode + Decode + Clone + Debug + Eq + PartialEq,
> {
	/// The balance.
	balance: Balance,
	/// Whether the account is frozen.
	is_frozen: bool,
}

// TODO: accounts holding funds must be in existence first, or...
//   `deposit` should be sufficient to allow for N additional accounts in the state,
//   and the creater can require a minimum balance here to ensure dust accounts don't use this up.

decl_storage! {
	trait Store for Module<T: Trait> as Assets {
		/// The number of units of assets held by any given account.
		Account: map hasher(blake2_128_concat) (T::AssetId, T::AccountId)
			=> AccountData<T::Balance>;

		/// The next asset identifier up for grabs.
		NextAssetId get(fn next_asset_id): T::AssetId;

		/// Details of an asset.
		Details: map hasher(twox_64_concat) T::AssetId => Option<AssetDetails<
			T::Balance,
			T::AccountId,
			BalanceOf<T>,
		>>;
	}
}

// TODO: force_create, allowing for an assets `virtuals` to be hot-wired.

decl_event! {
	pub enum Event<T> where
		<T as frame_system::Trait>::AccountId,
		<T as Trait>::Balance,
		<T as Trait>::AssetId,
	{
		/// Some assets were issued. \[asset_id, owner, total_supply\]
		Created(AssetId, AccountId, AccountId),
		/// Some assets were issued. \[asset_id, owner, total_supply\]
		Issued(AssetId, AccountId, Balance),
		/// Some assets were transferred. \[asset_id, from, to, amount\]
		Transferred(AssetId, AccountId, AccountId, Balance),
		/// Some assets were destroyed. \[asset_id, owner, balance\]
		Burned(AssetId, AccountId, Balance),
		/// The management team changed \[asset_id, issuer, admin, freezer\]
		TeamChanged(AssetId, AccountId, AccountId, AccountId),
		/// The owner changed \[asset_id, owner\]
		OwnerChanged(AssetId, AccountId),
		/// Some assets was transferred by an admin. \[asset_id, from, to, amount\]
		ForceTransferred(AssetId, AccountId, AccountId, Balance),
		/// Some account `who` was frozen. \[asset_id, who\]
		Frozen(AssetId, AccountId),
		/// Some account `who` was thawed. \[asset_id, who\]
		Thawed(AssetId, AccountId),
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Transfer amount should be non-zero
		AmountZero,
		/// Account balance must be greater than or equal to the transfer amount
		BalanceLow,
		/// Balance should be non-zero
		BalanceZero,
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// The given asset ID is unknown.
		Unknown,
		/// The origin account is frozen.
		Frozen,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Issue a new class of fungible assets. There are, and will only ever be, `total`
		/// such assets and they'll all belong to the `origin` initially. It will have an
		/// identifier `AssetId` instance: this will be specified in the `Issued` event.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 storage mutation (codec `O(1)`).
		/// - 2 storage writes (condec `O(1)`).
		/// - 1 event.
		/// # </weight>
		#[weight = 0]
		fn create(origin, owner: <T::Lookup as StaticLookup>::Source) {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			let id = Self::next_asset_id();
			NextAssetId::<T>::mutate(|id| *id += One::one());

			Details::<T>::insert(id, AssetDetails {
				owner: owner.clone(),
				issuer: owner.clone(),
				admin: owner.clone(),
				freezer: owner.clone(),
				supply: Zero::zero(),
				deposit: Zero::zero(),
				max_zombies: 0,
				minimum_balance: Zero::zero(),
			});
			Self::deposit_event(RawEvent::Created(id, origin, owner));
		}

		#[weight = 0]
		fn mint(origin,
			#[compact] id: T::AssetId,
			beneficiary: <T::Lookup as StaticLookup>::Source,
			#[compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			Details::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.issuer, Error::<T>::NoPermission);
				d.supply = d.supply.saturating_add(amount);
				Account::<T>::mutate((id, &beneficiary), |t|
					t.balance = t.balance.saturating_add(amount)
				);

				Self::deposit_event(RawEvent::Issued(id, beneficiary, amount));
				Ok(())
			})
		}

		/// Move some assets from one holder to another.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 static lookup
		/// - 2 storage mutations (codec `O(1)`).
		/// - 1 event.
		/// # </weight>
		#[weight = 0]
		fn transfer(origin,
			#[compact] id: T::AssetId,
			target: <T::Lookup as StaticLookup>::Source,
			#[compact] amount: T::Balance
		) {
			let origin = (id, ensure_signed(origin)?);
			ensure!(!amount.is_zero(), Error::<T>::AmountZero);

			let mut origin_account = Account::<T>::get(&origin);
			ensure!(!origin_account.is_frozen, Error::<T>::Frozen);
			origin_account.balance = origin_account.balance.checked_sub(&amount)
				.ok_or(Error::<T>::BalanceLow)?;

			let dest = (id, T::Lookup::lookup(target)?);

			if origin_account.balance.is_zero() {
				Account::<T>::remove(&origin);
			} else {
				Account::<T>::insert(&origin, origin_account);
			}
			Account::<T>::mutate(&dest, |a| a.balance = a.balance.saturating_add(amount));

			Self::deposit_event(RawEvent::Transferred(id, origin.1, dest.1, amount));
		}

		/// Destroy up to `amount` assets of `id` owned by `who`.
		///
		/// Origin must be Signed from the Manager account.
		///
		/// Bails with `BalanceZero` if the `who` is already dead.
		#[weight = 0]
		fn burn(origin,
			#[compact] id: T::AssetId,
			who: <T::Lookup as StaticLookup>::Source,
			#[compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			Details::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.admin, Error::<T>::NoPermission);

				let burned = Account::<T>::try_mutate_exists((id, &who), |maybe_account| {
					if let Some(mut account) = maybe_account.take() {
						let burned = amount.min(account.balance);
						account.balance -= burned;
						*maybe_account = if account.balance.is_zero() {
							None
						} else {
							Some(account)
						};
						Ok(burned)
					} else {
						Err(Error::<T>::BalanceZero)
					}
				})?;

				d.supply = d.supply.saturating_sub(burned);

				Self::deposit_event(RawEvent::Burned(id, who, burned));
				Ok(())
			})
		}

		#[weight = 0]
		fn set_owner(origin,
			#[compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Details::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.owner, Error::<T>::NoPermission);

				d.owner = owner.clone();

				Self::deposit_event(RawEvent::OwnerChanged(id, owner));
				Ok(())
			})
		}

		#[weight = 0]
		fn set_team(origin,
			#[compact] id: T::AssetId,
			issuer: <T::Lookup as StaticLookup>::Source,
			admin: <T::Lookup as StaticLookup>::Source,
			freezer: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let issuer = T::Lookup::lookup(issuer)?;
			let admin = T::Lookup::lookup(admin)?;
			let freezer = T::Lookup::lookup(freezer)?;

			Details::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.owner, Error::<T>::NoPermission);

				d.issuer = issuer.clone();
				d.admin = admin.clone();
				d.freezer = freezer.clone();

				Self::deposit_event(RawEvent::TeamChanged(id, issuer, admin, freezer));
				Ok(())
			})
		}

		#[weight = 0]
		fn freeze(origin, #[compact] id: T::AssetId, who: <T::Lookup as StaticLookup>::Source) {
			let origin = ensure_signed(origin)?;

			let d = Details::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.admin, Error::<T>::NoPermission);

			let who = (id, T::Lookup::lookup(who)?);
			Account::<T>::mutate(&who, |a| a.is_frozen = true);

			Self::deposit_event(Event::<T>::Frozen(id, who.1));
		}

		#[weight = 0]
		fn thaw(origin, #[compact] id: T::AssetId, who: <T::Lookup as StaticLookup>::Source) {
			let origin = ensure_signed(origin)?;

			let d = Details::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.admin, Error::<T>::NoPermission);

			let who = (id, T::Lookup::lookup(who)?);
			Account::<T>::mutate(&who, |a| a.is_frozen = false);

			Self::deposit_event(Event::<T>::Thawed(id, who.1));
		}

		#[weight = 0]
		fn force_transfer(origin,
			#[compact] id: T::AssetId,
			source: <T::Lookup as StaticLookup>::Source,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] amount: T::Balance,
		) {
			let origin = ensure_signed(origin)?;

			let d = Details::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.admin, Error::<T>::NoPermission);

			let source = (id, T::Lookup::lookup(source)?);
			let mut source_account = Account::<T>::get(&source);
			let amount = amount.min(source_account.balance);

			ensure!(!amount.is_zero(), Error::<T>::AmountZero);

			let dest = (id, T::Lookup::lookup(dest)?);

			source_account.balance -= amount;
			if source_account.balance.is_zero() {
				Account::<T>::remove(&source);
			} else {
				Account::<T>::insert(&source, source_account);
			}

			Account::<T>::mutate(&dest, |a| a.balance = a.balance.saturating_add(amount));

			Self::deposit_event(RawEvent::ForceTransferred(id, source.1, dest.1, amount));
		}
	}
}

// The main implementation block for the module.
impl<T: Trait> Module<T> {
	// Public immutables

	/// Get the asset `id` balance of `who`.
	pub fn balance(id: T::AssetId, who: T::AccountId) -> T::Balance {
		Account::<T>::get((id, who)).balance
	}

	/// Get the total supply of an asset `id`.
	pub fn total_supply(id: T::AssetId) -> T::Balance {
		Details::<T>::get(id).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{impl_outer_origin, assert_ok, assert_noop, parameter_types, weights::Weight};
	use sp_core::H256;
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type BaseCallFilter = ();
		type Origin = Origin;
		type Index = u64;
		type Call = ();
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumExtrinsicWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}

	impl pallet_balances::Trait for Test {
		type MaxLocks = ();
		type Balance = u64;
		type DustRemoval = ();
		type Event = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}

	impl Trait for Test {
		type Currency = Balances;
		type Event = ();
		type Balance = u64;
		type AssetId = u32;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Assets = Module<Test>;

	fn new_test_ext() -> sp_io::TestExternalities {
		frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
	}

	#[test]
	fn issuing_asset_units_to_issuer_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
		});
	}

	#[test]
	fn querying_total_supply_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
			assert_ok!(Assets::transfer(Origin::signed(2), 0, 3, 31));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 19);
			assert_eq!(Assets::balance(0, 3), 31);
			assert_ok!(Assets::burn(Origin::signed(1), 0, 3, u64::max_value()));
			assert_eq!(Assets::total_supply(0), 69);
		});
	}

	#[test]
	fn transferring_amount_above_available_balance_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
		});
	}

	#[test]
	fn transferring_amount_more_than_available_balance_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
			assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
			assert_eq!(Assets::balance(0, 1), 0);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 1, 50), Error::<Test>::BalanceLow);
		});
	}

	#[test]
	fn transferring_less_than_one_unit_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 0), Error::<Test>::AmountZero);
		});
	}

	#[test]
	fn transferring_more_units_than_total_supply_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 101), Error::<Test>::BalanceLow);
		});
	}

	#[test]
	fn destroying_asset_balance_with_positive_balance_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
		});
	}

	#[test]
	fn destroying_asset_balance_with_zero_balance_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::create(Origin::signed(1), 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 2), 0);
			assert_noop!(Assets::burn(Origin::signed(1), 0, 2, u64::max_value()), Error::<Test>::BalanceZero);
		});
	}
}
