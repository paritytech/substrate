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
//! * **Zombie**: An account which has a balance of some assets in this pallet, but no other
//!   footprint on-chain, in particular no account managed in the `frame_system` pallet.
//!
//! ### Goals
//!
//! The assets system in Substrate is designed to make the following possible:
//!
//! * Issue a new assets in a permissioned or permissionless way, if permissionless, then with a
//!   deposit required.
//! * Allow accounts to hold these assets without otherwise existing on-chain (*zombies*).
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
//!
//! ### Permissioned Functions
//!
//! * `force_create`: Creates a new asset class without taking any deposit.
//! * `force_destroy`: Destroys an asset class.
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

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

use sp_std::prelude::*;
use sp_runtime::{
	RuntimeDebug,
	traits::{
		AtLeast32BitUnsigned, Zero, StaticLookup, Saturating, CheckedSub, CheckedAdd,
	}
};
use codec::{Encode, Decode, HasCompact};
use frame_support::{
	ensure,
	traits::{Currency, ReservableCurrency, BalanceStatus::Reserved},
	dispatch::{DispatchError, DispatchResult},
};
pub use weights::WeightInfo;

pub use pallet::*;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

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
}

/// Witness data for the destroy transactions.
// TODO: make compact encoding.
#[derive(Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct DestroyWitness {
	/// The number of accounts holding the asset.
	accounts: u32,
	/// The number of accounts holding the asset with a self-sufficient reference.
	sufficients: u32,
	/// The number of transfer-approvals of the asset.
	approvals: u32,
}

// TODO: transaction to alter `is_sufficient`.

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{
		dispatch::DispatchResultWithPostInfo,
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

		/// The arithmetic type of asset identifier.
		type AssetId: Member + Parameter + Default + Copy + HasCompact;

		/// The currency mechanism.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The origin which may forcibly create or destroy an asset.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// The basic amount of funds that must be reserved for an asset.
		type AssetDeposit: Get<BalanceOf<Self>>;

		/// The basic amount of funds that must be reserved when adding metadata to your asset.
		type MetadataDepositBase: Get<BalanceOf<Self>>;

		/// The additional funds that must be reserved for the number of bytes you store in your
		/// metadata.
		type MetadataDepositPerByte: Get<BalanceOf<Self>>;

		/// The amount of funds that must be reserved when creating a new approval.
		type ApprovalDeposit: Get<BalanceOf<Self>>;

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
		AssetDetails<T::Balance, T::AccountId, BalanceOf<T>>
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
		ValueQuery
	>;

	#[pallet::storage]
	/// Approved balance transfers. First balance is the amount approved for transfer. Second
	/// is the amount of `T::Currency` reserved for storing this.
	pub(super) type Approvals<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		Blake2_128Concat,
		(T::AccountId, T::AccountId),
		(T::Balance, BalanceOf<T>),
		ValueQuery
	>;

	#[pallet::storage]
	/// Metadata of an asset.
	pub(super) type Metadata<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AssetId,
		AssetMetadata<BalanceOf<T>>,
		ValueQuery
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
		/// New metadata has been set for an asset. \[asset_id, name, symbol, decimals\]
		MetadataSet(T::AssetId, Vec<u8>, Vec<u8>, u8),
		/// Additional funds have been approved for transfer to a destination account.
		/// \[asset_id, source, destination, amount\]
		ApprovedTransfer(T::AssetId, T::AccountId, T::AccountId, T::Balance),
		/// An approval for account `beneficiary` was cancelled by `owner`.
		/// \[id, owner, beneficiary\]
		ApprovalCancelled(T::AssetId, T::AccountId, T::AccountId),
		/// An `amount` was transferred in its entirety from `owner` to `destination` by
		/// the approved `beneficiary`.
		/// \[id, owner, beneficiary, destination\]
		ApprovalTransferred(T::AssetId, T::AccountId, T::AccountId, T::AccountId, T::Balance),
	}

	#[deprecated(note = "use `Event` instead")]
	pub type RawEvent<T> = Event<T>;

	#[pallet::error]
	pub enum Error<T> {
		/// Transfer amount should be non-zero.
		AmountZero,
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
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Issue a new class of fungible assets from a public origin.
		///
		/// This new asset class has no assets initially.
		///
		/// The origin must be Signed and the sender must have sufficient funds free.
		///
		/// Funds of sender are reserved according to the formula:
		/// `AssetDepositBase + AssetDepositPerZombie * max_zombies`.
		///
		/// Parameters:
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
		/// Emits `Created` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::create())]
		pub(super) fn create(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			admin: <T::Lookup as StaticLookup>::Source,
			min_balance: T::Balance,
		) -> DispatchResultWithPostInfo {
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
			Ok(().into())
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
		) -> DispatchResultWithPostInfo {
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
			Ok(().into())
		}

		/// Destroy a class of fungible assets owned by the sender.
		///
		/// The origin must be Signed and the sender must be the owner of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be destroyed. This must identify an existing
		/// asset.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(c + p + a)` where:
		/// - `c = (witness.accounts - witness.sufficients)`
		/// - `p = witness.sufficients`
		/// - `a = witness.approvals`
//		#[pallet::weight(T::WeightInfo::force_destroy(
//			witness.accounts.saturating_sub(witness.sufficients),
// 			witness.sufficients,
// 			witness.approvals,
// 		))]
		#[pallet::weight(T::WeightInfo::destroy(witness.accounts.saturating_sub(witness.sufficients)))]
		pub(super) fn destroy(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			/*#[pallet::compact]*/ witness: DestroyWitness,
		) -> DispatchResultWithPostInfo {
			let check_owner = ensure_signed(origin)?;
			Ok(Self::do_destroy(id, witness, Some(check_owner))?.into())
		}

		/// Destroy a class of fungible assets.
		///
		/// The origin must conform to `ForceOrigin`.
		///
		/// - `id`: The identifier of the asset to be destroyed. This must identify an existing
		/// asset.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(c + p + a)` where:
		/// - `c = (witness.accounts - witness.sufficients)`
		/// - `p = witness.sufficients`
		/// - `a = witness.approvals`
//		#[pallet::weight(T::WeightInfo::force_destroy(
//			witness.accounts.saturating_sub(witness.sufficients),
// 			witness.sufficients,
// 			witness.approvals,
// 		))]
		#[pallet::weight(T::WeightInfo::force_destroy(witness.accounts.saturating_sub(witness.sufficients)))]
		pub(super) fn force_destroy(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			/*#[pallet::compact]*/ witness: DestroyWitness,
		) -> DispatchResultWithPostInfo {
			T::ForceOrigin::ensure_origin(origin)?;
			Ok(Self::do_destroy(id, witness, None)?.into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;

				ensure!(&origin == &details.issuer, Error::<T>::NoPermission);
				details.supply = details.supply.checked_add(&amount).ok_or(Error::<T>::Overflow)?;

				Account::<T>::try_mutate(id, &beneficiary, |t| -> DispatchResultWithPostInfo {
					let new_balance = t.balance.saturating_add(amount);
					ensure!(new_balance >= details.min_balance, Error::<T>::BalanceLow);
					if t.balance.is_zero() {
						t.sufficient = Self::new_account(&beneficiary, details)?;
					}
					t.balance = new_balance;
					Ok(().into())
				})?;
				Self::deposit_event(Event::Issued(id, beneficiary, amount));
				Ok(().into())
			})
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.admin, Error::<T>::NoPermission);

				let burned = Account::<T>::try_mutate_exists(
					id,
					&who,
					|maybe_account| -> Result<T::Balance, DispatchError> {
						let mut account = maybe_account.take().ok_or(Error::<T>::BalanceZero)?;
						let mut burned = amount.min(account.balance);
						account.balance -= burned;
						*maybe_account = if account.balance < d.min_balance {
							burned += account.balance;
							Self::dead_account(&who, d, account.sufficient);
							None
						} else {
							Some(account)
						};
						Ok(burned)
					}
				)?;

				d.supply = d.supply.saturating_sub(burned);

				Self::deposit_event(Event::Burned(id, who, burned));
				Ok(().into())
			})
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(target)?;

			Ok(Self::do_transfer(id, origin, dest, amount, None)?.into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let source = T::Lookup::lookup(source)?;
			let dest = T::Lookup::lookup(dest)?;

			Ok(Self::do_transfer(id, source, dest, amount, Some(origin))?.into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.freezer, Error::<T>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(Account::<T>::contains_key(id, &who), Error::<T>::BalanceZero);

			Account::<T>::mutate(id, &who, |a| a.is_frozen = true);

			Self::deposit_event(Event::<T>::Frozen(id, who));
			Ok(().into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;

			let details = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &details.admin, Error::<T>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(Account::<T>::contains_key(id, &who), Error::<T>::BalanceZero);

			Account::<T>::mutate(id, &who, |a| a.is_frozen = false);

			Self::deposit_event(Event::<T>::Thawed(id, who));
			Ok(().into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.freezer, Error::<T>::NoPermission);

				d.is_frozen = true;

				Self::deposit_event(Event::<T>::AssetFrozen(id));
				Ok(().into())
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &d.admin, Error::<T>::NoPermission);

				d.is_frozen = false;

				Self::deposit_event(Event::<T>::AssetThawed(id));
				Ok(().into())
			})
		}

		/// Change the Owner of an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// - `id`: The identifier of the asset to be frozen.
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
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Asset::<T>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T>::NoPermission);
				if details.owner == owner { return Ok(().into()) }

				let metadata_deposit = Metadata::<T>::get(id).deposit;
				let deposit = details.deposit + metadata_deposit;

				// Move the deposit to the new owner.
				T::Currency::repatriate_reserved(&details.owner, &owner, deposit, Reserved)?;

				details.owner = owner.clone();

				Self::deposit_event(Event::OwnerChanged(id, owner));
				Ok(().into())
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
		) -> DispatchResultWithPostInfo {
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
				Ok(().into())
			})
		}

		/// Set the metadata for an asset.
		///
		/// NOTE: There is no `unset_metadata` call. Simply pass an empty name, symbol,
		/// and 0 decimals to this function to remove the metadata of an asset and
		/// return your deposit.
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
		/// Emits `MaxZombiesChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_metadata(name.len() as u32, symbol.len() as u32))]
		pub(super) fn set_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);
			ensure!(symbol.len() <= T::StringLimit::get() as usize, Error::<T>::BadMetadata);

			let d = Asset::<T>::get(id).ok_or(Error::<T>::Unknown)?;
			ensure!(&origin == &d.owner, Error::<T>::NoPermission);

			Metadata::<T>::try_mutate_exists(id, |metadata| {
				let bytes_used = name.len() + symbol.len();
				let old_deposit = match metadata {
					Some(m) => m.deposit,
					None => Default::default()
				};

				// Metadata is being removed
				if bytes_used.is_zero() && decimals.is_zero() {
					T::Currency::unreserve(&origin, old_deposit);
					*metadata = None;
				} else {
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
					})
				}

				Self::deposit_event(Event::MetadataSet(id, name, symbol, decimals));
				Ok(().into())
			})
		}

		// TODO: Weight
		#[pallet::weight(0)]
		fn approve_transfer(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			beneficiary: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance,
		) -> DispatchResultWithPostInfo {
			let owner = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let key = (owner, beneficiary);
			Approvals::<T>::try_mutate(id, &key, |&mut (ref mut approved, ref mut deposit)| -> DispatchResult {
				let approval_deposit = T::ApprovalDeposit::get();
				if *deposit < approval_deposit {
					T::Currency::reserve(&key.0, approval_deposit - *deposit)?;
					*deposit = approval_deposit;
				}
				*approved = approved.saturating_add(amount);
				Ok(())
			})?;
			let (owner, beneficiary) = key;

			Self::deposit_event(Event::ApprovedTransfer(id, owner, beneficiary, amount));
			Ok(().into())
		}

		// TODO: Weight
		#[pallet::weight(0)]
		fn cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			beneficiary: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			let owner = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;
			let key = (owner, beneficiary);
			let approval = Approvals::<T>::take(id, &key);
			let (owner, beneficiary) = key;
			T::Currency::unreserve(&owner, approval.1);

			Self::deposit_event(Event::ApprovalCancelled(id, owner, beneficiary));
			Ok(().into())
		}

		// TODO: Weight
		#[pallet::weight(0)]
		fn transfer_approved(
			origin: OriginFor<T>,
			#[pallet::compact] id: T::AssetId,
			owner: <T::Lookup as StaticLookup>::Source,
			destination: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::Balance,
		) -> DispatchResultWithPostInfo {
			let beneficiary = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;
			let destination = T::Lookup::lookup(destination)?;

			let key = (owner, beneficiary);
			Approvals::<T>::try_mutate_exists(id, &key, |approved| -> DispatchResult {
				let (mut remaining, deposit) = approved.take().unwrap_or_default();
				ensure!(remaining >= amount, Error::<T>::Unapproved);
				remaining -= amount;
				if remaining.is_zero() {
					T::Currency::unreserve(&key.0, deposit);
				} else {
					*approved = Some((remaining, deposit));
				}
				Ok(())
			})?;
			let (owner, beneficiary) = key;
			Self::deposit_event(Event::ApprovalTransferred(id, owner, beneficiary, destination, amount));
			Ok(().into())
		}
	}
}

// The main implementation block for the module.
impl<T: Config> Pallet<T> {
	// Public immutables

	/// Get the asset `id` balance of `who`.
	pub fn balance(id: T::AssetId, who: T::AccountId) -> T::Balance {
		Account::<T>::get(id, who).balance
	}

	/// Get the total supply of an asset `id`.
	pub fn total_supply(id: T::AssetId) -> T::Balance {
		Asset::<T>::get(id).map(|x| x.supply).unwrap_or_else(Zero::zero)
	}

	fn new_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, BalanceOf<T>>,
	) -> Result<bool, DispatchError> {
		let accounts = d.accounts.checked_add(1).ok_or(Error::<T>::Overflow)?;
		let is_sufficient = if d.is_sufficient {
			frame_system::Module::<T>::inc_sufficients(who);
			d.sufficients += 1;
			true
		} else {
			frame_system::Module::<T>::inc_consumers(who).map_err(|_| Error::<T>::NoProvider)?;
			false
		};
		d.accounts = accounts;
		Ok(is_sufficient)
	}

	fn dead_account(
		who: &T::AccountId,
		d: &mut AssetDetails<T::Balance, T::AccountId, BalanceOf<T>>,
		sufficient: bool,
	) {
		if sufficient {
			d.sufficients = d.sufficients.saturating_sub(1);
			let e = frame_system::Module::<T>::dec_sufficients(who);
			debug_assert!(e.is_ok(), "Assets: Self-sufficient refcount underflow");
		} else {
			frame_system::Module::<T>::dec_consumers(who);
		}
		d.accounts = d.accounts.saturating_sub(1);
	}

	fn do_destroy(
		id: T::AssetId,
		witness: DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> DispatchResult {
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

			// TODO: could use postinfo to reflect the actual number of accounts/sufficient/approvals
			Ok(())
		})
	}

	fn do_transfer(
		id: T::AssetId,
		source: T::AccountId,
		dest: T::AccountId,
		amount: T::Balance,
		maybe_need_admin: Option<T::AccountId>,
	) -> DispatchResult {
		ensure!(!amount.is_zero(), Error::<T>::AmountZero);

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

			if dest == source {
				return Ok(())
			}

			let mut amount = amount;
			if source_account.balance < details.min_balance {
				amount += source_account.balance;
				source_account.balance = Zero::zero();
			}

			Account::<T>::try_mutate(id, &dest, |a| -> DispatchResult {
				let new_balance = a.balance.saturating_add(amount);

				// This is impossible since `new_balance > amount > min_balance`, but we can
				// handle it, so we do.
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

			Self::deposit_event(Event::Transferred(id, source, dest, amount));
			Ok(())
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_assets;

	use frame_support::{assert_ok, assert_noop, parameter_types};
	use sp_core::H256;
	use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::Header};
	use pallet_balances::Error as BalancesError;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Module, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Module, Call, Storage, Config<T>, Event<T>},
			Assets: pallet_assets::{Module, Call, Storage, Event<T>},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type Call = Call;
		type BlockNumber = u64;
		type Hash = H256;
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
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}

	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type Balance = u64;
		type DustRemoval = ();
		type Event = Event;
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}

	parameter_types! {
		pub const AssetDeposit: u64 = 1;
		pub const ApprovalDeposit: u64 = 1;
		pub const StringLimit: u32 = 50;
		pub const MetadataDepositBase: u64 = 1;
		pub const MetadataDepositPerByte: u64 = 1;
	}

	impl Config for Test {
		type Currency = Balances;
		type Event = Event;
		type Balance = u64;
		type AssetId = u32;
		type ForceOrigin = frame_system::EnsureRoot<u64>;
		type AssetDeposit = AssetDeposit;
		type StringLimit = StringLimit;
		type MetadataDepositBase = MetadataDepositBase;
		type MetadataDepositPerByte = MetadataDepositPerByte;
		type WeightInfo = ();
		type ApprovalDeposit = ApprovalDeposit;
	}

	pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
		frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
	}

	#[test]
	fn basic_minting_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::mint(Origin::signed(1), 0, 2, 100));
			assert_eq!(Assets::balance(0, 2), 100);
		});
	}

	#[test]
	fn lifecycle_should_work() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&1, 100);
			assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));
			assert_eq!(Balances::reserved_balance(&1), 1);
			assert!(Asset::<Test>::contains_key(0));

			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0], vec![0], 12));
			assert_eq!(Balances::reserved_balance(&1), 4);
			assert!(Metadata::<Test>::contains_key(0));

			Balances::make_free_balance_be(&10, 100);
			assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
			Balances::make_free_balance_be(&20, 100);
			assert_ok!(Assets::mint(Origin::signed(1), 0, 20, 100));
			assert_eq!(Account::<Test>::iter_prefix(0).count(), 2);

			let w = Asset::<Test>::get(0).unwrap().destroy_witness();
			assert_ok!(Assets::destroy(Origin::signed(1), 0, w));
			assert_eq!(Balances::reserved_balance(&1), 0);

			assert!(!Asset::<Test>::contains_key(0));
			assert!(!Metadata::<Test>::contains_key(0));
			assert_eq!(Account::<Test>::iter_prefix(0).count(), 0);

			assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));
			assert_eq!(Balances::reserved_balance(&1), 1);
			assert!(Asset::<Test>::contains_key(0));

			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0], vec![0], 12));
			assert_eq!(Balances::reserved_balance(&1), 4);
			assert!(Metadata::<Test>::contains_key(0));

			assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 20, 100));
			assert_eq!(Account::<Test>::iter_prefix(0).count(), 2);

			let w = Asset::<Test>::get(0).unwrap().destroy_witness();
			assert_ok!(Assets::force_destroy(Origin::root(), 0, w));
			assert_eq!(Balances::reserved_balance(&1), 0);

			assert!(!Asset::<Test>::contains_key(0));
			assert!(!Metadata::<Test>::contains_key(0));
			assert_eq!(Account::<Test>::iter_prefix(0).count(), 0);
		});
	}

	#[test]
	fn destroy_with_bad_witness_should_not_work() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&1, 100);
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			let w = Asset::<Test>::get(0).unwrap().destroy_witness();
			assert_ok!(Assets::mint(Origin::signed(1), 0, 10, 100));
			assert_noop!(Assets::destroy(Origin::signed(1), 0, w), Error::<Test>::BadWitness);
			assert_noop!(Assets::force_destroy(Origin::root(), 0, w), Error::<Test>::BadWitness);
		});
	}

	#[test]
	fn non_providing_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, false, 1));

			Balances::make_free_balance_be(&0, 100);
			assert_ok!(Assets::mint(Origin::signed(1), 0, 0, 100));

			// Cannot mint into account 2 since it doesn't (yet) exist...
			assert_noop!(Assets::mint(Origin::signed(1), 0, 1, 100), Error::<Test>::NoProvider);
			// ...or transfer...
			assert_noop!(Assets::transfer(Origin::signed(0), 0, 1, 50), Error::<Test>::NoProvider);
			// ...or force-transfer
			assert_noop!(Assets::force_transfer(Origin::signed(1), 0, 0, 1, 50), Error::<Test>::NoProvider);

			Balances::make_free_balance_be(&1, 100);
			Balances::make_free_balance_be(&2, 100);
			assert_ok!(Assets::transfer(Origin::signed(0), 0, 1, 25));
			assert_ok!(Assets::force_transfer(Origin::signed(1), 0, 0, 2, 25));
		});
	}

	#[test]
	fn min_balance_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 10));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

			// Cannot create a new account with a balance that is below minimum...
			assert_noop!(Assets::mint(Origin::signed(1), 0, 2, 9), Error::<Test>::BalanceLow);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 9), Error::<Test>::BalanceLow);
			assert_noop!(Assets::force_transfer(Origin::signed(1), 0, 1, 2, 9), Error::<Test>::BalanceLow);

			// When deducting from an account to below minimum, it should be reaped.

			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 91));
			assert!(Assets::balance(0, 1).is_zero());
			assert_eq!(Assets::balance(0, 2), 100);
			assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

			assert_ok!(Assets::force_transfer(Origin::signed(1), 0, 2, 1, 91));
			assert!(Assets::balance(0, 2).is_zero());
			assert_eq!(Assets::balance(0, 1), 100);
			assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 1);

			assert_ok!(Assets::burn(Origin::signed(1), 0, 1, 91));
			assert!(Assets::balance(0, 1).is_zero());
			assert_eq!(Asset::<Test>::get(0).unwrap().accounts, 0);
		});
	}

	#[test]
	fn querying_total_supply_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
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
	fn transferring_amount_below_available_balance_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
		});
	}

	#[test]
	fn transferring_frozen_user_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::freeze(Origin::signed(1), 0, 1));
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 50), Error::<Test>::Frozen);
			assert_ok!(Assets::thaw(Origin::signed(1), 0, 1));
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		});
	}

	#[test]
	fn transferring_frozen_asset_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::freeze_asset(Origin::signed(1), 0));
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 50), Error::<Test>::Frozen);
			assert_ok!(Assets::thaw_asset(Origin::signed(1), 0));
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
		});
	}

	#[test]
	fn origin_guards_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_noop!(Assets::transfer_ownership(Origin::signed(2), 0, 2), Error::<Test>::NoPermission);
			assert_noop!(Assets::set_team(Origin::signed(2), 0, 2, 2, 2), Error::<Test>::NoPermission);
			assert_noop!(Assets::freeze(Origin::signed(2), 0, 1), Error::<Test>::NoPermission);
			assert_noop!(Assets::thaw(Origin::signed(2), 0, 2), Error::<Test>::NoPermission);
			assert_noop!(Assets::mint(Origin::signed(2), 0, 2, 100), Error::<Test>::NoPermission);
			assert_noop!(Assets::burn(Origin::signed(2), 0, 1, 100), Error::<Test>::NoPermission);
			assert_noop!(Assets::force_transfer(Origin::signed(2), 0, 1, 2, 100), Error::<Test>::NoPermission);
			let w = Asset::<Test>::get(0).unwrap().destroy_witness();
			assert_noop!(Assets::destroy(Origin::signed(2), 0, w), Error::<Test>::NoPermission);
		});
	}

	#[test]
	fn transfer_owner_should_work() {
		new_test_ext().execute_with(|| {
			Balances::make_free_balance_be(&1, 100);
			Balances::make_free_balance_be(&2, 100);
			assert_ok!(Assets::create(Origin::signed(1), 0, 1, 1));

			assert_eq!(Balances::reserved_balance(&1), 1);

			assert_ok!(Assets::transfer_ownership(Origin::signed(1), 0, 2));
			assert_eq!(Balances::reserved_balance(&2), 1);
			assert_eq!(Balances::reserved_balance(&1), 0);

			assert_noop!(Assets::transfer_ownership(Origin::signed(1), 0, 1), Error::<Test>::NoPermission);

			// Set metadata now and make sure that deposit gets transferred back.
			assert_ok!(Assets::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12));
			assert_ok!(Assets::transfer_ownership(Origin::signed(2), 0, 1));
			assert_eq!(Balances::reserved_balance(&1), 22);
			assert_eq!(Balances::reserved_balance(&2), 0);
		});
	}

	#[test]
	fn set_team_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::set_team(Origin::signed(1), 0, 2, 3, 4));

			assert_ok!(Assets::mint(Origin::signed(2), 0, 2, 100));
			assert_ok!(Assets::freeze(Origin::signed(4), 0, 2));
			assert_ok!(Assets::thaw(Origin::signed(3), 0, 2));
			assert_ok!(Assets::force_transfer(Origin::signed(3), 0, 2, 3, 100));
			assert_ok!(Assets::burn(Origin::signed(3), 0, 3, 100));
		});
	}

	#[test]
	fn transferring_to_frozen_account_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 2, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_eq!(Assets::balance(0, 2), 100);
			assert_ok!(Assets::freeze(Origin::signed(1), 0, 2));
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 2), 150);
		});
	}

	#[test]
	fn transferring_amount_more_than_available_balance_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::transfer(Origin::signed(1), 0, 2, 50));
			assert_eq!(Assets::balance(0, 1), 50);
			assert_eq!(Assets::balance(0, 2), 50);
			assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
			assert_eq!(Assets::balance(0, 1), 0);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 1, 50), Error::<Test>::BalanceLow);
			assert_noop!(Assets::transfer(Origin::signed(2), 0, 1, 51), Error::<Test>::BalanceLow);
		});
	}

	#[test]
	fn transferring_less_than_one_unit_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 0), Error::<Test>::AmountZero);
		});
	}

	#[test]
	fn transferring_more_units_than_total_supply_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_noop!(Assets::transfer(Origin::signed(1), 0, 2, 101), Error::<Test>::BalanceLow);
		});
	}

	#[test]
	fn burning_asset_balance_with_positive_balance_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 1), 100);
			assert_ok!(Assets::burn(Origin::signed(1), 0, 1, u64::max_value()));
			assert_eq!(Assets::balance(0, 1), 0);
		});
	}

	#[test]
	fn burning_asset_balance_with_zero_balance_should_not_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
			assert_eq!(Assets::balance(0, 2), 0);
			assert_noop!(Assets::burn(Origin::signed(1), 0, 2, u64::max_value()), Error::<Test>::BalanceZero);
		});
	}

	#[test]
	fn set_metadata_should_work() {
		new_test_ext().execute_with(|| {
			// Cannot add metadata to unknown asset
			assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::Unknown,
			);
			assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
			// Cannot add metadata to unowned asset
			assert_noop!(
				Assets::set_metadata(Origin::signed(2), 0, vec![0u8; 10], vec![0u8; 10], 12),
				Error::<Test>::NoPermission,
			);

			// Cannot add oversized metadata
			assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 100], vec![0u8; 10], 12),
				Error::<Test>::BadMetadata,
			);
			assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 100], 12),
				Error::<Test>::BadMetadata,
			);

			// Successfully add metadata and take deposit
			Balances::make_free_balance_be(&1, 30);
			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 10], 12));
			assert_eq!(Balances::free_balance(&1), 9);

			// Update deposit
			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 5], 12));
			assert_eq!(Balances::free_balance(&1), 14);
			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 10], vec![0u8; 15], 12));
			assert_eq!(Balances::free_balance(&1), 4);

			// Cannot over-reserve
			assert_noop!(
				Assets::set_metadata(Origin::signed(1), 0, vec![0u8; 20], vec![0u8; 20], 12),
				BalancesError::<Test, _>::InsufficientBalance,
			);

			// Clear Metadata
			assert!(Metadata::<Test>::contains_key(0));
			assert_ok!(Assets::set_metadata(Origin::signed(1), 0, vec![], vec![], 0));
			assert!(!Metadata::<Test>::contains_key(0));
		});
	}
}
