// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
//! * Asset Issuance (Minting)
//! * Asset Transferal
//! * Asset Freezing
//! * Asset Destruction (Burning)
//! * Delegated Asset Transfers ("Approval API")
//!
//! To use it in your runtime, you need to implement the assets [`Config`].
//!
//! The supported dispatchable functions are documented in the [`Call`] enum.
//!
//! ### Terminology
//!
//! * **Admin**: An account ID uniquely privileged to be able to unfreeze (thaw) an account and it's
//!   assets, as well as forcibly transfer a particular class of assets between arbitrary accounts
//!   and reduce the balance of a particular class of assets of arbitrary accounts.
//! * **Asset issuance/minting**: The creation of a new asset, whose total supply will belong to the
//!   account that issues the asset. This is a privileged operation.
//! * **Asset transfer**: The reduction of the balance of an asset of one account with the
//!   corresponding increase in the balance of another.
//! * **Asset destruction**: The process of reduce the balance of an asset of one account. This is
//!   a privileged operation.
//! * **Fungible asset**: An asset whose units are interchangeable.
//! * **Issuer**: An account ID uniquely privileged to be able to mint a particular class of assets.
//! * **Freezer**: An account ID uniquely privileged to be able to freeze an account from
//!   transferring a particular class of assets.
//! * **Freezing**: Removing the possibility of an unpermissioned transfer of an asset from a
//!   particular account.
//! * **Non-fungible asset**: An asset for which each unit has unique characteristics.
//! * **Owner**: An account ID uniquely privileged to be able to destroy a particular asset class,
//!   or to set the Issuer, Freezer or Admin of that asset class.
//! * **Approval**: The act of allowing an account the permission to transfer some
//!   balance of asset from the approving account into some third-party destination account.
//! * **Sufficiency**: The idea of a minimum-balance of an asset being sufficient to allow the
//!   account's existence on the system without requiring any other existential-deposit.
//!
//! ### Goals
//!
//! The assets system in Substrate is designed to make the following possible:
//!
//! * Issue a new assets in a permissioned or permissionless way, if permissionless, then with a
//!   deposit required.
//! * Allow accounts to be delegated the ability to transfer assets without otherwise existing
//!   on-chain (*approvals*).
//! * Move assets between accounts.
//! * Update the asset's total supply.
//! * Allow administrative activities by specially privileged accounts including freezing account
//!   balances and minting/burning assets.
//!
//! ## Interface
//!
//! ### Permissionless Functions
//!
//! * `create`: Creates a new asset class, taking the required deposit.
//! * `transfer`: Transfer sender's assets to another account.
//! * `transfer_keep_alive`: Transfer sender's assets to another account, keeping the sender alive.
//! * `set_metadata`: Set the metadata of an asset class.
//! * `clear_metadata`: Remove the metadata of an asset class.
//! * `approve_transfer`: Create or increase an delegated transfer.
//! * `cancel_approval`: Rescind a previous approval.
//! * `transfer_approved`: Transfer third-party's assets to another account.
//!
//! ### Permissioned Functions
//!
//! * `force_create`: Creates a new asset class without taking any deposit.
//! * `force_set_metadata`: Set the metadata of an asset class.
//! * `force_clear_metadata`: Remove the metadata of an asset class.
//! * `force_asset_status`: Alter an asset class's attributes.
//! * `force_cancel_approval`: Rescind a previous approval.
//!
//! ### Privileged Functions
//! * `destroy`: Destroys an entire asset class; called by the asset class's Owner.
//! * `mint`: Increases the asset balance of an account; called by the asset class's Issuer.
//! * `burn`: Decreases the asset balance of an account; called by the asset class's Admin.
//! * `force_transfer`: Transfers between arbitrary accounts; called by the asset class's Admin.
//! * `freeze`: Disallows further `transfer`s from an account; called by the asset class's Freezer.
//! * `thaw`: Allows further `transfer`s from an account; called by the asset class's Admin.
//! * `transfer_ownership`: Changes an asset class's Owner; called by the asset class's Owner.
//! * `set_team`: Changes an asset class's Admin, Freezer and Issuer; called by the asset class's
//!   Owner.
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
//! ## Related Modules
//!
//! * [`System`](../frame_system/index.html)
//! * [`Support`](../frame_support/index.html)

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

pub mod weights;
#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;

use sp_std::prelude::*;
use sp_runtime::{
	RuntimeDebug,
	traits::{
		AtLeast32BitUnsigned, Zero, StaticLookup, Saturating, CheckedSub, CheckedAdd,
	}
};
use codec::{Encode, Decode, HasCompact};
use frame_support::{ensure, dispatch::{DispatchError, DispatchResult}};
use frame_support::traits::{Currency, ReservableCurrency, BalanceStatus::Reserved};
use frame_support::traits::tokens::{WithdrawConsequence, DepositConsequence, fungibles};
use frame_system::Config as SystemConfig;

pub use weights::WeightInfo;
pub use pallet::*;

impl<T: Config> fungibles::Inspect<<T as SystemConfig>::AccountId> for Pallet<T> {
	type AssetId = T::AssetId;
	type Balance = T::Balance;

	fn total_issuance(asset: Self::AssetId) -> Self::Balance {
		Asset::<T>::get(asset).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}

	fn minimum_balance(asset: Self::AssetId) -> Self::Balance {
		Asset::<T>::get(asset).map(|x| x.min_balance).unwrap_or_else(Zero::zero)
	}

	fn balance(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
	) -> Self::Balance {
		Pallet::<T>::balance(asset, who)
	}

	fn can_deposit(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) -> DepositConsequence {
		Pallet::<T>::can_deposit(asset, who, amount)
	}

	fn can_withdraw(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance> {
		Pallet::<T>::can_withdraw(asset, who, amount)
	}
}

impl<T: Config> fungibles::Mutate<<T as SystemConfig>::AccountId> for Pallet<T> {
	fn deposit(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		Pallet::<T>::increase_balance(asset, who.clone(), amount, None)
	}

	fn withdraw(
		asset: Self::AssetId,
		who: &<T as SystemConfig>::AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		Pallet::<T>::reduce_balance(asset, who.clone(), amount, None)
	}
}

impl<T: Config> fungibles::Transfer<T::AccountId> for Pallet<T> {
	fn transfer(
		asset: Self::AssetId,
		source: &T::AccountId,
		dest: &T::AccountId,
		amount: T::Balance,
	) -> Result<T::Balance, DispatchError> {
		<Self as fungibles::Mutate::<T::AccountId>>::transfer(asset, source, dest, amount)
	}
}

type DepositBalanceOf<T> = <<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct AssetDetails<
	Balance,
	AccountId,
	DepositBalance,
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
	/// The balance deposited for this asset. This pays for the data stored here.
	deposit: DepositBalance,
	/// The ED for virtual accounts.
	min_balance: Balance,
	/// If `true`, then any account with this asset is given a provider reference. Otherwise, it
	/// requires a consumer reference.
	is_sufficient: bool,
	/// The total number of accounts.
	accounts: u32,
	/// The total number of accounts for which we have placed a self-sufficient reference.
	sufficients: u32,
	/// The total number of approvals.
	approvals: u32,
	/// Whether the asset is frozen for non-admin transfers.
	is_frozen: bool,
}

impl<Balance, AccountId, DepositBalance> AssetDetails<Balance, AccountId, DepositBalance> {
	pub fn destroy_witness(&self) -> DestroyWitness {
		DestroyWitness {
			accounts: self.accounts,
			sufficients: self.sufficients,
			approvals: self.approvals,
		}
	}
}

/// A pair to act as a key for the approval storage map.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct ApprovalKey<AccountId> {
	/// The owner of the funds that are being approved.
	owner: AccountId,
	/// The party to whom transfer of the funds is being delegated.
	delegate: AccountId,
}

/// Data concerning an approval.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default)]
pub struct Approval<Balance, DepositBalance> {
	/// The amount of funds approved for the balance transfer from the owner to some delegated
	/// target.
	amount: Balance,
	/// The amount reserved on the owner's account to hold this item in storage.
	deposit: DepositBalance,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default)]
pub struct AssetBalance<Balance> {
	/// The balance.
	balance: Balance,
	/// Whether the account is frozen.
	is_frozen: bool,
	/// `true` if this balance gave the account a self-sufficient reference.
	sufficient: bool,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default)]
pub struct AssetMetadata<DepositBalance> {
	/// The balance deposited for this metadata.
	///
	/// This pays for the data stored in this struct.
	deposit: DepositBalance,
	/// The user friendly name of this asset. Limited in length by `StringLimit`.
	name: Vec<u8>,
	/// The ticker symbol for this asset. Limited in length by `StringLimit`.
	symbol: Vec<u8>,
	/// The number of decimals this asset uses to represent one unit.
	decimals: u8,
	/// Whether the asset metadata may be changed by a non Force origin.
	is_frozen: bool,
}

/// Witness data for the destroy transactions.
#[derive(Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct DestroyWitness {
	/// The number of accounts holding the asset.
	#[codec(compact)]
	accounts: u32,
	/// The number of accounts holding the asset with a self-sufficient reference.
	#[codec(compact)]
	sufficients: u32,
	/// The number of transfer-approvals of the asset.
	#[codec(compact)]
	approvals: u32,
}

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{
		dispatch::DispatchResult,
		pallet_prelude::*,
	};
	use frame_system::pallet_prelude::*;
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	/// The module configuration trait.
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The units in which we record balances.
		type Balance: Member + Parameter + AtLeast32BitUnsigned + Default + Copy;

		/// Identifier for the class of asset.
		type AssetId: Member + Parameter + Default + Copy + HasCompact;

		/// The currency mechanism.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The origin which may forcibly create or destroy an asset or otherwise alter privileged
		/// attributes.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// The basic amount of funds that must be reserved for an asset.
		type AssetDeposit: Get<DepositBalanceOf<Self>>;

		/// The basic amount of funds that must be reserved when adding metadata to your asset.
		type MetadataDepositBase: Get<DepositBalanceOf<Self>>;

		/// The additional funds that must be reserved for the number of bytes you store in your
		/// metadata.
		type MetadataDepositPerByte: Get<DepositBalanceOf<Self>>;

		/// The amount of funds that must be reserved when creating a new approval.
		type ApprovalDeposit: Get<DepositBalanceOf<Self>>;

		/// The maximum length of a name or symbol stored on-chain.
		type StringLimit: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::storage]
	/// Details of an asset.
	pub(super) type Asset<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T>>,
	>;

	#[pallet::storage]
	/// The number of units of assets held by any given account.
	pub(super) type Account<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		Blake2_128Concat,
		T::AccountId,
		AssetBalance<T::Balance>,
		ValueQuery,
	>;

	#[pallet::storage]
	/// Approved balance transfers. First balance is the amount approved for transfer. Second
	/// is the amount of `T::Currency` reserved for storing this.
	pub(super) type Approvals<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		Blake2_128Concat,
		ApprovalKey<T::AccountId>,
		Approval<T::Balance, DepositBalanceOf<T>>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Metadata of an asset.
	pub(super) type Metadata<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		AssetMetadata<DepositBalanceOf<T>>,
		ValueQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	#[pallet::metadata(T::AccountId = "AccountId", T::Balance = "Balance", T::AssetId = "AssetId")]
	pub enum Event<T: Config> {
		/// Some asset class was created. \[asset_id, creator, owner\]
		Created(T::AssetId, T::AccountId, T::AccountId),
		/// Some assets were issued. \[asset_id, owner, total_supply\]
		Issued(T::AssetId, T::AccountId, T::Balance),
		/// Some assets were transferred. \[asset_id, from, to, amount\]
		Transferred(T::AssetId, T::AccountId, T::AccountId, T::Balance),
		/// Some assets were destroyed. \[asset_id, owner, balance\]
		Burned(T::AssetId, T::AccountId, T::Balance),
		/// The management team changed \[asset_id, issuer, admin, freezer\]
		TeamChanged(T::AssetId, T::AccountId, T::AccountId, T::AccountId),
		/// The owner changed \[asset_id, owner\]
		OwnerChanged(T::AssetId, T::AccountId),
		/// Some account `who` was frozen. \[asset_id, who\]
		Frozen(T::AssetId, T::AccountId),
		/// Some account `who` was thawed. \[asset_id, who\]
		Thawed(T::AssetId, T::AccountId),
		/// Some asset `asset_id` was frozen. \[asset_id\]
		AssetFrozen(T::AssetId),
		/// Some asset `asset_id` was thawed. \[asset_id\]
		AssetThawed(T::AssetId),
		/// An asset class was destroyed.
		Destroyed(T::AssetId),
		/// Some asset class was force-created. \[asset_id, owner\]
		ForceCreated(T::AssetId, T::AccountId),
		/// New metadata has been set for an asset. \[asset_id, name, symbol, decimals, is_frozen\]
		MetadataSet(T::AssetId, Vec<u8>, Vec<u8>, u8, bool),
		/// Metadata has been cleared for an asset. \[asset_id\]
		MetadataCleared(T::AssetId),
		/// (Additional) funds have been approved for transfer to a destination account.
		/// \[asset_id, source, delegate, amount\]
		ApprovedTransfer(T::AssetId, T::AccountId, T::AccountId, T::Balance),
		/// An approval for account `delegate` was cancelled by `owner`.
		/// \[id, owner, delegate\]
		ApprovalCancelled(T::AssetId, T::AccountId, T::AccountId),
		/// An `amount` was transferred in its entirety from `owner` to `destination` by
		/// the approved `delegate`.
		/// \[id, owner, delegate, destination\]
		TransferredApproved(T::AssetId, T::AccountId, T::AccountId, T::AccountId, T::Balance),
		/// An asset has had its attributes changed by the `Force` origin.
		/// \[id\]
		AssetStatusChanged(T::AssetId),
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Account balance must be greater than or equal to the transfer amount.
		BalanceLow,
		/// Balance should be non-zero.
		BalanceZero,
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// The given asset ID is unknown.
		Unknown,
		/// The origin account is frozen.
		Frozen,
		/// The asset ID is already taken.
		InUse,
		/// Invalid witness data given.
		BadWitness,
		/// Minimum balance should be non-zero.
		MinBalanceZero,
		/// A mint operation lead to an overflow.
		Overflow,
		/// No provider reference exists to allow a non-zero balance of a non-self-sufficient asset.
		NoProvider,
		/// Invalid metadata given.
		BadMetadata,
		/// No approval exists that would allow the transfer.
		Unapproved,
		/// The source account would not survive the transfer and it needs to stay alive.
		WouldDie,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Issue a new class of fungible assets from a public origin.
		///
		/// This new asset class has no assets initially and its owner is the origin.
		///
		/// The origin must be Signed and the sender must have sufficient funds free.
		///
		/// Funds of sender are reserved by `AssetDeposit`.
		///
		/// Parameters:
		/// - `id`: The identifier of the new asset. This must not be currently in use to identify
		/// an existing asset.
		/// - `admin`: The admin of this class of assets. The admin is the initial address of each
		/// member of the asset class's admin team.
		/// - `min_balance`: The minimum balance of this new asset that any single account must
		/// have. If an account's balance is reduced below this, then it collapses to zero.
		///
		/// Emits `Created` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::create())]
		pub(super) fn create(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			admin: <T::Lookup as StaticLookup>::Source,
			min_balance: T::Balance,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let admin = T::Lookup::lookup(admin)?;

			ensure!(!Asset::<T>::contains_key(id), Error::<T>::InUse);
			ensure!(!min_balance.is_zero(), Error::<T>::MinBalanceZero);

			let deposit = T::AssetDeposit::get();
			T::Currency::reserve(&owner, deposit)?;

			Asset::<T>::insert(id, AssetDetails {
				owner: owner.clone(),
				issuer: admin.clone(),
				admin: admin.clone(),
				freezer: admin.clone(),
				supply: Zero::zero(),
				deposit,
				min_balance,
				is_sufficient: false,
				accounts: 0,
				sufficients: 0,
				approvals: 0,
				is_frozen: false,
			});
			Self::deposit_event(Event::Created(id, owner, admin));
			Ok(())
		}

		/// Issue a new class of fungible assets from a privileged origin.
		///
		/// This new asset class has no assets initially.
		///
		/// The origin must conform to `ForceOrigin`.
		///
		/// Unlike `create`, no funds are reserved.
		///
		/// - `id`: The identifier of the new asset. This must not be currently in use to identify
		/// an existing asset.
		/// - `owner`: The owner of this class of assets. The owner has full superuser permissions
		/// over this asset, but may later change and configure the permissions using `transfer_ownership`
		/// and `set_team`.
		/// - `max_zombies`: The total number of accounts which may hold assets in this class yet
		/// have no existential deposit.
		/// - `min_balance`: The minimum balance of this new asset that any single account must
		/// have. If an account's balance is reduced below this, then it collapses to zero.
		///
		/// Emits `ForceCreated` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_create())]
		pub(super) fn force_create(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
			is_sufficient: bool,
			#[pallet::compact] min_balance: T::Balance,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			ensure!(!Asset::<T>::contains_key(id), Error::<T>::InUse);
			ensure!(!min_balance.is_zero(), Error::<T>::MinBalanceZero);

			Asset::<T>::insert(id, AssetDetails {
				owner: owner.clone(),
				issuer: owner.clone(),
				admin: owner.clone(),
				freezer: owner.clone(),
				supply: Zero::zero(),
				deposit: Zero::zero(),
				min_balance,
				is_sufficient,
				accounts: 0,
				sufficients: 0,
				approvals: 0,
				is_frozen: false,
			});
			Self::deposit_event(Event::ForceCreated(id, owner));
			Ok(())
		}

		/// Destroy a class of fungible assets.
		///
		/// The origin must conform to `ForceOrigin` or must be Signed and the sender must be the
		/// owner of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be destroyed. This must identify an existing
		/// asset.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(c + p + a)` where:
		/// - `c = (witness.accounts - witness.sufficients)`
		/// - `s = witness.sufficients`
		/// - `a = witness.approvals`
		#[pallet::weight(T::WeightInfo::destroy(
			witness.accounts.saturating_sub(witness.sufficients),
 			witness.sufficients,
 			witness.approvals,
 		))]
		pub(super) fn destroy(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			witness: DestroyWitness,
		) -> DispatchResult {
			let maybe_check_owner = match T::ForceOrigin::try_origin(origin) {
				Ok(_) => None,
				Err(origin) => Some(ensure_signed(origin)?),
			};
			Asset::<T>::try_mutate_exists(id, |maybe_details| {
				let mut details = maybe_details.take().ok_or(Error::<T>::Unknown)?;
				if let Some(check_owner) = maybe_check_owner {
					ensure!(details.owner == check_owner, Error::<T>::NoPermission);
				}
				ensure!(details.accounts == witness.accounts, Error::<T>::BadWitness);
				ensure!(details.sufficients == witness.sufficients, Error::<T>::BadWitness);
				ensure!(details.approvals == witness.approvals, Error::<T>::BadWitness);

				for (who, v) in Account::<T>::drain_prefix(id) {
					Self::dead_account(&who, &mut details, v.sufficient);
				}
				debug_assert_eq!(details.accounts, 0);
				debug_assert_eq!(details.sufficients, 0);

				let metadata = Metadata::<T>::take(&id);
				T::Currency::unreserve(&details.owner, details.deposit.saturating_add(metadata.deposit));

				Approvals::<T>::remove_prefix(&id);
				Self::deposit_event(Event::Destroyed(id));

				// NOTE: could use postinfo to reflect the actual number of accounts/sufficient/approvals
				Ok(())
			})
		}

		/// Mint assets of a particular class.
		///
		/// The origin must be Signed and the sender must be the Issuer of the asset `id`.
		///
		/// - `id`: The identifier of the asset to have some amount minted.
		/// - `beneficiary`: The account to be credited with the minted assets.
		/// - `amount`: The amount of the asset to be minted.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(1)`
		/// Modes: Pre-existing balance of `beneficiary`; Account pre-existence of `beneficiary`.
		#[pallet::weight(T::WeightInfo::mint())]
		pub(super) fn mint(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			beneficiary: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;
			Self::increase_balance(id, beneficiary, amount, Some(origin))
		}

		/// Reduce the balance of `who` by as much as possible up to `amount` assets of `id`.
		///
		/// Origin must be Signed and the sender should be the Manager of the asset `id`.
		///
		/// Bails with `BalanceZero` if the `who` is already dead.
		///
		/// - `id`: The identifier of the asset to have some amount burned.
		/// - `who`: The account to be debited from.
		/// - `amount`: The maximum amount by which `who`'s balance should be reduced.
		///
		/// Emits `Burned` with the actual amount burned. If this takes the balance to below the
		/// minimum for the asset, then the amount burned is increased to take it to zero.
		///
		/// Weight: `O(1)`
		/// Modes: Post-existence of `who`; Pre & post Zombie-status of `who`.
		#[pallet::weight(T::WeightInfo::burn())]
		pub(super) fn burn(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			who: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			Self::reduce_balance(id, who, amount, Some(origin)).map(|_| ())
		}

		/// Move some assets from the sender account to another.
		///
		/// Origin must be Signed.
		///
		/// - `id`: The identifier of the asset to have some amount transferred.
		/// - `target`: The account to be credited.
		/// - `amount`: The amount by which the sender's balance of assets should be reduced and
		/// `target`'s balance increased. The amount actually transferred may be slightly greater in
		/// the case that the transfer would otherwise take the sender balance above zero but below
		/// the minimum balance. Must be greater than zero.
		///
		/// Emits `Transferred` with the actual amount transferred. If this takes the source balance
		/// to below the minimum for the asset, then the amount transferred is increased to take it
		/// to zero.
		///
		/// Weight: `O(1)`
		/// Modes: Pre-existence of `target`; Post-existence of sender; Prior & post zombie-status
		/// of sender; Account pre-existence of `target`.
		#[pallet::weight(T::WeightInfo::transfer())]
		pub(super) fn transfer(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			target: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(target)?;

			Self::do_transfer(id, origin, dest, amount, None, false)
		}

		/// Move some assets from the sender account to another, keeping the sender account alive.
		///
		/// Origin must be Signed.
		///
		/// - `id`: The identifier of the asset to have some amount transferred.
		/// - `target`: The account to be credited.
		/// - `amount`: The amount by which the sender's balance of assets should be reduced and
		/// `target`'s balance increased. The amount actually transferred may be slightly greater in
		/// the case that the transfer would otherwise take the sender balance above zero but below
		/// the minimum balance. Must be greater than zero.
		///
		/// Emits `Transferred` with the actual amount transferred. If this takes the source balance
		/// to below the minimum for the asset, then the amount transferred is increased to take it
		/// to zero.
		///
		/// Weight: `O(1)`
		/// Modes: Pre-existence of `target`; Post-existence of sender; Prior & post zombie-status
		/// of sender; Account pre-existence of `target`.
		#[pallet::weight(T::WeightInfo::transfer_keep_alive())]
		pub(super) fn transfer_keep_alive(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			target: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(target)?;

			Self::do_transfer(id, origin, dest, amount, None, true)
		}

		/// Move some assets from one account to another.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `id`: The identifier of the asset to have some amount transferred.
		/// - `source`: The account to be debited.
		/// - `dest`: The account to be credited.
		/// - `amount`: The amount by which the `source`'s balance of assets should be reduced and
		/// `dest`'s balance increased. The amount actually transferred may be slightly greater in
		/// the case that the transfer would otherwise take the `source` balance above zero but
		/// below the minimum balance. Must be greater than zero.
		///
		/// Emits `Transferred` with the actual amount transferred. If this takes the source balance
		/// to below the minimum for the asset, then the amount transferred is increased to take it
		/// to zero.
		///
		/// Weight: `O(1)`
		/// Modes: Pre-existence of `dest`; Post-existence of `source`; Prior & post zombie-status
		/// of `source`; Account pre-existence of `dest`.
		#[pallet::weight(T::WeightInfo::force_transfer())]
		pub(super) fn force_transfer(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			source: <T::Lookup as StaticLookup>::Source,
			dest: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let source = T::Lookup::lookup(source)?;
			let dest = T::Lookup::lookup(dest)?;

			Self::do_transfer(id, source, dest, amount, Some(origin), false)
		}

		/// Disallow further unprivileged transfers from an account.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
		/// - `who`: The account to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze())]
		pub(super) fn freeze(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			who: <T::Lookup as StaticLookup>::Source
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.freezer, Error::<T>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(Account::<T>::contains_key(id, &who), Error::<T>::BalanceZero);

			Account::<T>::mutate(id, &who, |a| a.is_frozen = true);

			Self::deposit_event(Event::<T>::Frozen(id, who));
			Ok(())
		}

		/// Allow unprivileged transfers from an account again.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
		/// - `who`: The account to be unfrozen.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw())]
		pub(super) fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact]
			id: T::AssetId,
			who: <T::Lookup as StaticLookup>::Source
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let details = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &details.admin, Error::<T>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(Account::<T>::contains_key(id, &who), Error::<T>::BalanceZero);

			Account::<T>::mutate(id, &who, |a| a.is_frozen = false);

			Self::deposit_event(Event::<T>::Thawed(id, who));
			Ok(())
		}

		/// Disallow further unprivileged transfers for the asset class.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze_asset())]
		pub(super) fn freeze_asset(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.freezer, Error::<T>::NoPermission);

				d.is_frozen = true;

				Self::deposit_event(Event::<T>::AssetFrozen(id));
				Ok(())
			})
		}

		/// Allow unprivileged transfers for the asset again.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw_asset())]
		pub(super) fn thaw_asset(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.admin, Error::<T>::NoPermission);

				d.is_frozen = false;

				Self::deposit_event(Event::<T>::AssetThawed(id));
				Ok(())
			})
		}

		/// Change the Owner of an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// - `id`: The identifier of the asset.
		/// - `owner`: The new Owner of this asset.
		///
		/// Emits `OwnerChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer_ownership())]
		pub(super) fn transfer_ownership(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T>::NoPermission);
				if details.owner == owner { return Ok(()) }

				let metadata_deposit = Metadata::<T>::get(id).deposit;
				let deposit = details.deposit + metadata_deposit;

				// Move the deposit to the new owner.
				T::Currency::repatriate_reserved(&details.owner, &owner, deposit, Reserved)?;

				details.owner = owner.clone();

				Self::deposit_event(Event::OwnerChanged(id, owner));
				Ok(())
			})
		}

		/// Change the Issuer, Admin and Freezer of an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
		/// - `issuer`: The new Issuer of this asset.
		/// - `admin`: The new Admin of this asset.
		/// - `freezer`: The new Freezer of this asset.
		///
		/// Emits `TeamChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_team())]
		pub(super) fn set_team(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			issuer: <T::Lookup as StaticLookup>::Source,
			admin: <T::Lookup as StaticLookup>::Source,
			freezer: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let issuer = T::Lookup::lookup(issuer)?;
			let admin = T::Lookup::lookup(admin)?;
			let freezer = T::Lookup::lookup(freezer)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T>::NoPermission);

				details.issuer = issuer.clone();
				details.admin = admin.clone();
				details.freezer = freezer.clone();

				Self::deposit_event(Event::TeamChanged(id, issuer, admin, freezer));
				Ok(())
			})
		}

		/// Set the metadata for an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// Funds of sender are reserved according to the formula:
		/// `MetadataDepositBase + MetadataDepositPerByte * (name.len + symbol.len)` taking into
		/// account any already reserved funds.
		///
		/// - `id`: The identifier of the asset to update.
		/// - `name`: The user friendly name of this asset. Limited in length by `StringLimit`.
		/// - `symbol`: The exchange symbol for this asset. Limited in length by `StringLimit`.
		/// - `decimals`: The number of decimals this asset uses to represent one unit.
		///
		/// Emits `MetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_metadata(name.len() as u32, symbol.len() as u32))]
		pub(super) fn set_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);
			ensure!(symbol.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.owner, Error::<T>::NoPermission);

			Metadata::<T>::try_mutate_exists(id, |metadata| {
				ensure!(metadata.as_ref().map_or(true, |m| !m.is_frozen), Error::<T>::NoPermission);

				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				let new_deposit = T::MetadataDepositPerByte::get()
					.saturating_mul(((name.len() + symbol.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());

				if new_deposit > old_deposit {
					T::Currency::reserve(&origin, new_deposit - old_deposit)?;
				} else {
					T::Currency::unreserve(&origin, old_deposit - new_deposit);
				}

				*metadata = Some(AssetMetadata {
					deposit: new_deposit,
					name: name.clone(),
					symbol: symbol.clone(),
					decimals,
					is_frozen: false,
				});

				Self::deposit_event(Event::MetadataSet(id, name, symbol, decimals, false));
				Ok(())
			})
		}

		/// Clear the metadata for an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// Any deposit is freed for the asset owner.
		///
		/// - `id`: The identifier of the asset to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::clear_metadata())]
		pub(super) fn clear_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.owner, Error::<T>::NoPermission);

			Metadata::<T>::try_mutate_exists(id, |metadata| {
				let deposit = metadata.take().ok_or(Error::<T>::Unknown)?.deposit;
				T::Currency::unreserve(&d.owner, deposit);
				Self::deposit_event(Event::MetadataCleared(id));
				Ok(())
			})
		}

		/// Force the metadata for an asset to some value.
		///
		/// Origin must be ForceOrigin.
		///
		/// Any deposit is left alone.
		///
		/// - `id`: The identifier of the asset to update.
		/// - `name`: The user friendly name of this asset. Limited in length by `StringLimit`.
		/// - `symbol`: The exchange symbol for this asset. Limited in length by `StringLimit`.
		/// - `decimals`: The number of decimals this asset uses to represent one unit.
		///
		/// Emits `MetadataSet`.
		///
		/// Weight: `O(N + S)` where N and S are the length of the name and symbol respectively.
		#[pallet::weight(T::WeightInfo::force_set_metadata(name.len() as u32, symbol.len() as u32))]
		pub(super) fn force_set_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);
			ensure!(symbol.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);

			ensure!(Asset::<T>::contains_key(id), Error::<T>::Unknown);
			Metadata::<T>::try_mutate_exists(id, |metadata| {
				let deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				*metadata = Some(AssetMetadata {
					deposit,
					name: name.clone(),
					symbol: symbol.clone(),
					decimals,
					is_frozen,
				});

				Self::deposit_event(Event::MetadataSet(id, name, symbol, decimals, is_frozen));
				Ok(())
			})
		}

		/// Clear the metadata for an asset.
		///
		/// Origin must be ForceOrigin.
		///
		/// Any deposit is returned.
		///
		/// - `id`: The identifier of the asset to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_clear_metadata())]
		pub(super) fn force_clear_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			Metadata::<T>::try_mutate_exists(id, |metadata| {
				let deposit = metadata.take().ok_or(Error::<T>::Unknown)?.deposit;
				T::Currency::unreserve(&d.owner, deposit);
				Self::deposit_event(Event::MetadataCleared(id));
				Ok(())
			})
		}

		/// Alter the attributes of a given asset.
		///
		/// Origin must be `ForceOrigin`.
		///
		/// - `id`: The identifier of the asset.
		/// - `owner`: The new Owner of this asset.
		/// - `issuer`: The new Issuer of this asset.
		/// - `admin`: The new Admin of this asset.
		/// - `freezer`: The new Freezer of this asset.
		/// - `min_balance`: The minimum balance of this new asset that any single account must
		/// have. If an account's balance is reduced below this, then it collapses to zero.
		/// - `is_sufficient`: Whether a non-zero balance of this asset is deposit of sufficient
		/// value to account for the state bloat associated with its balance storage. If set to
		/// `true`, then non-zero balances may be stored without a `consumer` reference (and thus
		/// an ED in the Balances pallet or whatever else is used to control user-account state
		/// growth).
		/// - `is_frozen`: Whether this asset class is frozen except for permissioned/admin
		/// instructions.
		///
		/// Emits `AssetStatusChanged` with the identity of the asset.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_asset_status())]
		pub(super) fn force_asset_status(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
			issuer: <T::Lookup as StaticLookup>::Source,
			admin: <T::Lookup as StaticLookup>::Source,
			freezer: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] min_balance: T::Balance,
			is_sufficient: bool,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			Asset::<T>::try_mutate(id, |maybe_asset| {
				let mut asset = maybe_asset.take().ok_or(Error::<T>::Unknown)?;
				asset.owner = T::Lookup::lookup(owner)?;
				asset.issuer = T::Lookup::lookup(issuer)?;
				asset.admin = T::Lookup::lookup(admin)?;
				asset.freezer = T::Lookup::lookup(freezer)?;
				asset.min_balance = min_balance;
				asset.is_sufficient = is_sufficient;
				asset.is_frozen = is_frozen;
				*maybe_asset = Some(asset);

				Self::deposit_event(Event::AssetStatusChanged(id));
				Ok(())
			})
		}

		/// Approve an amount of asset for transfer by a delegated third-party account.
		///
		/// Origin must be Signed.
		///
		/// Ensures that `ApprovalDeposit` worth of `Currency` is reserved from signing account
		/// for the purpose of holding the approval. If some non-zero amount of assets is already
		/// approved from signing account to `delegate`, then it is topped up or unreserved to
		/// meet the right value.
		///
		/// NOTE: The signing account does not need to own `amount` of assets at the point of
		/// making this call.
		///
		/// - `id`: The identifier of the asset.
		/// - `delegate`: The account to delegate permission to transfer asset.
		/// - `amount`: The amount of asset that may be transferred by `delegate`. If there is
		/// already an approval in place, then this acts additively.
		///
		/// Emits `ApprovedTransfer` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::approve_transfer())]
		pub(super) fn approve_transfer(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			delegate: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;

			let key = ApprovalKey { owner, delegate };
			Approvals::<T>::try_mutate(id, &key, |maybe_approved| -> DispatchResult {
				let mut approved = maybe_approved.take().unwrap_or_default();
				let deposit_required = T::ApprovalDeposit::get();
				if approved.deposit < deposit_required {
					T::Currency::reserve(&key.owner, deposit_required - approved.deposit)?;
					approved.deposit = deposit_required;
				}
				approved.amount = approved.amount.saturating_add(amount);
				*maybe_approved = Some(approved);
				Ok(())
			})?;
			Self::deposit_event(Event::ApprovedTransfer(id, key.owner, key.delegate, amount));

			Ok(())
		}

		/// Cancel all of some asset approved for delegated transfer by a third-party account.
		///
		/// Origin must be Signed and there must be an approval in place between signer and
		/// `delegate`.
		///
		/// Unreserves any deposit previously reserved by `approve_transfer` for the approval.
		///
		/// - `id`: The identifier of the asset.
		/// - `delegate`: The account delegated permission to transfer asset.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::cancel_approval())]
		pub(super) fn cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			let key = ApprovalKey { owner, delegate };
			let approval = Approvals::<T>::take(id, &key).ok_or(Error::<T>::Unknown)?;
			T::Currency::unreserve(&key.owner, approval.deposit);

			Self::deposit_event(Event::ApprovalCancelled(id, key.owner, key.delegate));
			Ok(())
		}

		/// Cancel all of some asset approved for delegated transfer by a third-party account.
		///
		/// Origin must be either ForceOrigin or Signed origin with the signer being the Admin
		/// account of the asset `id`.
		///
		/// Unreserves any deposit previously reserved by `approve_transfer` for the approval.
		///
		/// - `id`: The identifier of the asset.
		/// - `delegate`: The account delegated permission to transfer asset.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_cancel_approval())]
		pub(super) fn force_cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::ForceOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(|origin| -> DispatchResult {
					let origin = ensure_signed(origin)?;
					let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
					ensure!(&origin == &d.admin, Error::<T>::NoPermission);
					Ok(())
				})?;

			let owner = T::Lookup::lookup(owner)?;
			let delegate = T::Lookup::lookup(delegate)?;

			let key = ApprovalKey { owner, delegate };
			let approval = Approvals::<T>::take(id, &key).ok_or(Error::<T>::Unknown)?;
			T::Currency::unreserve(&key.owner, approval.deposit);

			Self::deposit_event(Event::ApprovalCancelled(id, key.owner, key.delegate));
			Ok(())
		}

		/// Transfer some asset balance from a previously delegated account to some third-party
		/// account.
		///
		/// Origin must be Signed and there must be an approval in place by the `owner` to the
		/// signer.
		///
		/// If the entire amount approved for transfer is transferred, then any deposit previously
		/// reserved by `approve_transfer` is unreserved.
		///
		/// - `id`: The identifier of the asset.
		/// - `owner`: The account which previously approved for a transfer of at least `amount` and
		/// from which the asset balance will be withdrawn.
		/// - `destination`: The account to which the asset balance of `amount` will be transferred.
		/// - `amount`: The amount of assets to transfer.
		///
		/// Emits `TransferredApproved` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer_approved())]
		pub(super) fn transfer_approved(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
			destination: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance,
		) -> DispatchResult {
			let delegate = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;
			let destination = T::Lookup::lookup(destination)?;

			let key = ApprovalKey { owner, delegate };
			Approvals::<T>::try_mutate_exists(id, &key, |maybe_approved| -> DispatchResult {
				let mut approved = maybe_approved.take().ok_or(Error::<T>::Unapproved)?;
				let remaining = approved.amount.checked_sub(&amount).ok_or(Error::<T>::Unapproved)?;

				Self::do_transfer(id, key.owner.clone(), destination, amount, None, false)?;

				if remaining.is_zero() {
					T::Currency::unreserve(&key.owner, approved.deposit);
				} else {
					approved.amount = remaining;
					*maybe_approved = Some(approved);
				}
				Ok(())
			})?;
			Ok(())
		}
	}
}

// The main implementation block for the module.
impl<T: Config> Pallet<T> {
	// Public immutables

	/// Get the asset `id` balance of `who`.
	pub fn balance(id: T::AssetId, who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Account::<T>::get(id, who.borrow()).balance
	}

	/// Get the total supply of an asset `id`.
	pub fn total_supply(id: T::AssetId) -> T::Balance {
		Asset::<T>::get(id).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}

	fn new_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T>>,
	) -> Result<bool, DispatchError> {
		let accounts = d.accounts.checked_add(1).ok_or(Error::<T>::Overflow)?;
		let is_sufficient = if d.is_sufficient {
			frame_system::Pallet::<T>::inc_sufficients(who);
			d.sufficients += 1;
			true
		} else {
			frame_system::Pallet::<T>::inc_consumers(who).map_err(|_| Error::<T>::NoProvider)?;
			false
		};
		d.accounts = accounts;
		Ok(is_sufficient)
	}

	fn dead_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, DepositBalanceOf<T>>,
		sufficient: bool,
	) {
		if sufficient {
			d.sufficients = d.sufficients.saturating_sub(1);
			frame_system::Pallet::<T>::dec_sufficients(who);
		} else {
			frame_system::Pallet::<T>::dec_consumers(who);
		}
		d.accounts = d.accounts.saturating_sub(1);
	}

	fn can_deposit(id: T::AssetId, who: &T::AccountId, amount: T::Balance) -> DepositConsequence {
		let details = match Asset::<T>::get(id) {
			Some(details) => details,
			None => return DepositConsequence::UnknownAsset,
		};
		if details.supply.checked_add(&amount).is_none() {
			return DepositConsequence::Overflow
		}
		let account = Account::<T>::get(id, who);
		if account.balance.checked_add(&amount).is_none() {
			return DepositConsequence::Overflow
		}
		if account.balance.is_zero() {
			if amount < details.min_balance {
				return DepositConsequence::BelowMinimum
			}
			if !details.is_sufficient && frame_system::Pallet::<T>::providers(who) == 0 {
				return DepositConsequence::CannotCreate
			}
			if details.is_sufficient && details.sufficients.checked_add(1).is_none() {
				return DepositConsequence::Overflow
			}
		}

		DepositConsequence::Success
	}

	fn can_withdraw(
		id: T::AssetId,
		who: &T::AccountId,
		amount: T::Balance,
	) -> WithdrawConsequence<T::Balance> {
		let details = match Asset::<T>::get(id) {
			Some(details) => details,
			None => return WithdrawConsequence::UnknownAsset,
		};
		if details.supply.checked_sub(&amount).is_none() {
			return WithdrawConsequence::Underflow
		}
		let account = Account::<T>::get(id, who);
		if let Some(rest) = account.balance.checked_sub(&amount) {
			if rest < details.min_balance {
				WithdrawConsequence::ReducedToZero(rest)
			} else {
				// NOTE: this assumes (correctly) that the token won't be a provider. If that ever
				// changes, this will need to change.
				WithdrawConsequence::Success
			}
		} else {
			WithdrawConsequence::NoFunds
		}
	}

	fn increase_balance(
		id: T::AssetId,
		beneficiary: T::AccountId,
		amount: T::Balance,
		maybe_check_issuer: Option<T::AccountId>,
	) -> DispatchResult {
		Asset::<T>::try_mutate(id, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;

			if let Some(check_issuer) = maybe_check_issuer {
				ensure!(&check_issuer == &details.issuer, Error::<T>::NoPermission);
			}
			details.supply = details.supply.checked_add(&amount).ok_or(Error::<T>::Overflow)?;

			Account::<T>::try_mutate(id, &beneficiary, |t| -> DispatchResult {
				let new_balance = t.balance.saturating_add(amount);
				ensure!(new_balance >= details.min_balance, Error::<T>::BalanceLow);
				if t.balance.is_zero() {
					t.sufficient = Self::new_account(&beneficiary, details)?;
				}
				t.balance = new_balance;
				Ok(())
			})?;
			Self::deposit_event(Event::Issued(id, beneficiary, amount));
			Ok(())
		})
	}

	fn reduce_balance(
		id: T::AssetId,
		target: T::AccountId,
		amount: T::Balance,
		maybe_check_admin: Option<T::AccountId>,
	) -> Result<T::Balance, DispatchError> {
		Asset::<T>::try_mutate(id, |maybe_details| {
			let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
			if let Some(check_admin) = maybe_check_admin {
				ensure!(&check_admin == &d.admin, Error::<T>::NoPermission);
			}

			let burned = Account::<T>::try_mutate_exists(
				id,
				&target,
				|maybe_account| -> Result<T::Balance, DispatchError> {
					let mut account = maybe_account.take().ok_or(Error::<T>::BalanceZero)?;
					let mut burned = amount.min(account.balance);
					account.balance -= burned;
					*maybe_account = if account.balance < d.min_balance {
						burned += account.balance;
						Self::dead_account(&target, d, account.sufficient);
						None
					} else {
						Some(account)
					};
					Ok(burned)
				}
			)?;

			d.supply = d.supply.saturating_sub(burned);

			Self::deposit_event(Event::Burned(id, target, burned));
			Ok(burned)
		})
	}

	fn do_transfer(
		id: T::AssetId,
		source: T::AccountId,
		dest: T::AccountId,
		amount: T::Balance,
		maybe_need_admin: Option<T::AccountId>,
		keep_alive: bool,
	) -> DispatchResult {
		let mut source_account = Account::<T>::get(id, &source);
		ensure!(!source_account.is_frozen, Error::<T>::Frozen);

		source_account.balance = source_account.balance.checked_sub(&amount)
			.ok_or(Error::<T>::BalanceLow)?;

		Asset::<T>::try_mutate(id, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
			ensure!(!details.is_frozen, Error::<T>::Frozen);

			if let Some(need_admin) = maybe_need_admin {
				ensure!(&need_admin == &details.admin, Error::<T>::NoPermission);
			}

			if dest != source && !amount.is_zero() {
				let mut amount = amount;
				if source_account.balance < details.min_balance {
					ensure!(!keep_alive, Error::<T>::WouldDie);
					amount += source_account.balance;
					source_account.balance = Zero::zero();
				}

				Account::<T>::try_mutate(id, &dest, |a| -> DispatchResult {
					let new_balance = a.balance.saturating_add(amount);

					ensure!(new_balance >= details.min_balance, Error::<T>::BalanceLow);

					if a.balance.is_zero() {
						a.sufficient = Self::new_account(&dest, details)?;
					}
					a.balance = new_balance;
					Ok(())
				})?;

				if source_account.balance.is_zero() {
					Self::dead_account(&source, details, source_account.sufficient);
					Account::<T>::remove(id, &source);
				} else {
					Account::<T>::insert(id, &source, &source_account)
				}
			}

			Self::deposit_event(Event::Transferred(id, source, dest, amount));
			Ok(())
		})
	}
}
