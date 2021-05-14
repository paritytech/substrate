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

//! # Unique (Assets) Module
//!
//! A simple, secure module for dealing with non-fungible assets.
//!
//! ## Related Modules
//!
//! * [`System`](../frame_system/index.html)
//! * [`Support`](../frame_support/index.html)

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

pub mod weights;
/* TODO:
#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
*/
/* TODO:
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;
*/
// TODO: mod impl_non_fungibles;
mod functions;
mod types;
pub use types::*;

use sp_std::prelude::*;
use sp_runtime::{RuntimeDebug, ArithmeticError, traits::{Zero, StaticLookup, Saturating}};
use codec::{Encode, Decode, HasCompact};
use frame_support::traits::{Currency, ReservableCurrency};
use frame_system::Config as SystemConfig;

pub use weights::WeightInfo;
pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	/// The module configuration trait.
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// Identifier for the class of asset.
		type ClassId: Member + Parameter + Default + Copy + HasCompact;

		/// The type used to identify a unique asset within an asset class.
		type InstanceId: Member + Parameter + Default + Copy + HasCompact;

		/// The currency mechanism, used for paying for reserves.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The origin which may forcibly create or destroy an asset or otherwise alter privileged
		/// attributes.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// The basic amount of funds that must be reserved for an asset class.
		type ClassDeposit: Get<DepositBalanceOf<Self, I>>;

		/// The basic amount of funds that must be reserved for an asset instance.
		type InstanceDeposit: Get<DepositBalanceOf<Self, I>>;

		/// The basic amount of funds that must be reserved when adding metadata to your asset.
		type MetadataDepositBase: Get<DepositBalanceOf<Self, I>>;

		/// The additional funds that must be reserved for the number of bytes you store in your
		/// metadata.
		type MetadataDepositPerByte: Get<DepositBalanceOf<Self, I>>;

		/// The amount of funds that must be reserved when creating a new approval.
		type ApprovalDeposit: Get<DepositBalanceOf<Self, I>>;

		/// The maximum length of a name or symbol stored on-chain.
		type StringLimit: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::storage]
	/// Details of an asset class.
	pub(super) type Class<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::ClassId,
		ClassDetails<T::AccountId, DepositBalanceOf<T, I>>,
	>;

	#[pallet::storage]
	/// The assets held by any given account; set out this way so that assets owned by a single
	/// account can be enumerated.
	pub(super) type Account<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		(T::ClassId, T::InstanceId),
		(),
		OptionQuery,
	>;

	#[pallet::storage]
	/// The assets in existence and their ownership details.
	pub(super) type Asset<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::ClassId,
		Blake2_128Concat,
		T::InstanceId,
		InstanceDetails<T::AccountId, DepositBalanceOf<T, I>>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Metadata of an asset class.
	pub(super) type ClassMetadataOf<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::ClassId,
		ClassMetadata<DepositBalanceOf<T, I>>,
		ValueQuery,
	>;

	#[pallet::storage]
	/// Metadata of an asset instance.
	pub(super) type InstanceMetadataOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::ClassId,
		Blake2_128Concat,
		T::InstanceId,
		InstanceMetadata<DepositBalanceOf<T, I>>,
		ValueQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	#[pallet::metadata(
		T::AccountId = "AccountId",
		T::ClassId = "AssetId",
		T::InstanceId = "InstanceId",
	)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// Some asset class was created. \[class, creator, owner\]
		Created(T::ClassId, T::AccountId, T::AccountId),
		/// Some asset class was force-created. \[asset_id, owner\]
		ForceCreated(T::ClassId, T::AccountId),
		/// An asset class was destroyed.
		Destroyed(T::ClassId),
		/// Some assets were issued. \[class, instance, owner\]
		Issued(T::ClassId, T::InstanceId, T::AccountId),
		/// Some assets were transferred. \[class, instance, from, to\]
		Transferred(T::ClassId, T::InstanceId, T::AccountId, T::AccountId),
		/// Some assets were destroyed. \[class, instance, owner\]
		Burned(T::ClassId, T::InstanceId, T::AccountId),
		/*
		/// The management team changed \[asset_id, issuer, admin, freezer\]
		TeamChanged(T::ClassId, T::AccountId, T::AccountId, T::AccountId),
		/// The owner changed \[asset_id, owner\]
		OwnerChanged(T::ClassId, T::AccountId),
		/// Some account `who` was frozen. \[asset_id, who\]
		Frozen(T::ClassId, T::AccountId),
		/// Some account `who` was thawed. \[asset_id, who\]
		Thawed(T::ClassId, T::AccountId),
		/// Some asset `asset_id` was frozen. \[asset_id\]
		AssetFrozen(T::ClassId),
		/// Some asset `asset_id` was thawed. \[asset_id\]
		AssetThawed(T::ClassId),
		/// New metadata has been set for an asset. \[asset_id, name, symbol, decimals, is_frozen\]
		MetadataSet(T::ClassId, Vec<u8>, Vec<u8>, u8, bool),
		/// Metadata has been cleared for an asset. \[asset_id\]
		MetadataCleared(T::ClassId),
		/// (Additional) funds have been approved for transfer to a destination account.
		/// \[asset_id, source, delegate, amount\]
		ApprovedTransfer(T::ClassId, T::InstanceId, T::AccountId, T::AccountId),
		/// An approval for account `delegate` was cancelled by `owner`.
		/// \[id, owner, delegate\]
		ApprovalCancelled(T::ClassId, T::AccountId, T::AccountId),
		/// An `amount` was transferred in its entirety from `owner` to `destination` by
		/// the approved `delegate`.
		/// \[id, owner, delegate, destination\]
		TransferredApproved(T::ClassId, T::InstanceId, T::AccountId, T::AccountId, T::AccountId),
		/// An asset has had its attributes changed by the `Force` origin.
		/// \[id\]
		AssetStatusChanged(T::ClassId),
		*/
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// The given asset ID is unknown.
		Unknown,
		/// The asset instance ID has already been used for an asset.
		AlreadyExists,
		/// The owner turned out to be different to what was expected.
		WrongOwner,
		/// Invalid witness data given.
		BadWitness,
		/// The asset ID is already taken.
		InUse,
/*
		/// The origin account is frozen.
		Frozen,
		/// Invalid metadata given.
		BadMetadata,
		/// No approval exists that would allow the transfer.
		Unapproved,
*/
	}

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Issue a new class of non-fungible assets from a public origin.
		///
		/// This new asset class has no assets initially and its owner is the origin.
		///
		/// The origin must be Signed and the sender must have sufficient funds free.
		///
		/// Funds of sender are reserved by `AssetDeposit`.
		///
		/// Parameters:
		/// - `class`: The identifier of the new asset class. This must not be currently in use to
		/// identify an existing asset.
		/// - `admin`: The admin of this class of assets. The admin is the initial address of each
		/// member of the asset class's admin team.
		///
		/// Emits `Created` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::create())]
		pub(super) fn create(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			admin: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let admin = T::Lookup::lookup(admin)?;

			ensure!(!Class::<T, I>::contains_key(class), Error::<T, I>::InUse);

			let deposit = T::ClassDeposit::get();
			T::Currency::reserve(&owner, deposit)?;

			Class::<T, I>::insert(
				class,
				ClassDetails {
					owner: owner.clone(),
					issuer: admin.clone(),
					admin: admin.clone(),
					freezer: admin.clone(),
					deposit,
					free_holding: false,
					instances: 0,
					free_holds: 0,
					is_frozen: false,
				},
			);
			Self::deposit_event(Event::Created(class, owner, admin));
			Ok(())
		}

		/// Issue a new class of non-fungible assets from a privileged origin.
		///
		/// This new asset class has no assets initially.
		///
		/// The origin must conform to `ForceOrigin`.
		///
		/// Unlike `create`, no funds are reserved.
		///
		/// - `class`: The identifier of the new asset. This must not be currently in use to identify
		/// an existing asset.
		/// - `owner`: The owner of this class of assets. The owner has full superuser permissions
		/// over this asset, but may later change and configure the permissions using `transfer_ownership`
		/// and `set_team`.
		///
		/// Emits `ForceCreated` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_create())]
		pub(super) fn force_create(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			owner: <T::Lookup as StaticLookup>::Source,
			free_holding: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			ensure!(!Class::<T, I>::contains_key(class), Error::<T, I>::InUse);

			Class::<T, I>::insert(
				class,
				ClassDetails {
					owner: owner.clone(),
					issuer: owner.clone(),
					admin: owner.clone(),
					freezer: owner.clone(),
					deposit: Zero::zero(),
					free_holding,
					instances: 0,
					free_holds: 0,
					is_frozen: false,
				},
			);
			Self::deposit_event(Event::ForceCreated(class, owner));
			Ok(())
		}

		/// Destroy a class of fungible assets.
		///
		/// The origin must conform to `ForceOrigin` or must be `Signed` and the sender must be the
		/// owner of the asset `id`.
		///
		/// - `class`: The identifier of the asset to be destroyed. This must identify an existing
		/// asset.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(c + p + a)` where:
		/// - `c = (witness.accounts - witness.sufficients)`
		/// - `s = witness.sufficients`
		#[pallet::weight(T::WeightInfo::destroy(
			witness.instances.saturating_sub(witness.free_holds),
 			witness.free_holds,
 		))]
		pub(super) fn destroy(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			witness: DestroyWitness,
		) -> DispatchResult {
			let maybe_check_owner = match T::ForceOrigin::try_origin(origin) {
				Ok(_) => None,
				Err(origin) => Some(ensure_signed(origin)?),
			};
			Class::<T, I>::try_mutate_exists(class, |maybe_details| {
				let mut class_details = maybe_details.take().ok_or(Error::<T, I>::Unknown)?;
				if let Some(check_owner) = maybe_check_owner {
					ensure!(class_details.owner == check_owner, Error::<T, I>::NoPermission);
				}
				ensure!(class_details.instances == witness.instances, Error::<T, I>::BadWitness);
				ensure!(class_details.free_holds == witness.free_holds, Error::<T, I>::BadWitness);

				for (instance, mut details) in Asset::<T, I>::drain_prefix(class) {
					Account::<T, I>::remove(&details.owner, (class, instance));
					Self::dead_instance(&mut details, &mut class_details);
				}
				debug_assert_eq!(class_details.instances, 0);
				debug_assert_eq!(class_details.free_holds, 0);

				let metadata = ClassMetadataOf::<T, I>::take(&class);
				T::Currency::unreserve(
					&class_details.owner,
					class_details.deposit.saturating_add(metadata.deposit),
				);

				Self::deposit_event(Event::Destroyed(class));

				// NOTE: could use postinfo to reflect the actual number of accounts/sufficient/approvals
				Ok(())
			})
		}

		/// Mint an asset instance of a particular class.
		///
		/// The origin must be Signed and the sender must be the Issuer of the asset `id`.
		///
		/// - `class`: The class of the asset to be minted.
		/// - `instance`: The instance value of the asset to be minted.
		/// - `beneficiary`: The account to be credited with the minted asset.
		///
		/// Emits `Issued` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::mint())]
		pub(super) fn mint(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			beneficiary: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			ensure!(!Asset::<T, I>::contains_key(class, instance), Error::<T, I>::AlreadyExists);

			Class::<T, I>::try_mutate(&class, |maybe_class_details| -> DispatchResult {
				let class_details = maybe_class_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(class_details.issuer == origin, Error::<T, I>::NoPermission);
				let details = Self::new_instance(beneficiary.clone(), None, class_details)?;
				Asset::<T, I>::insert(&class, &instance, details);
				Ok(())
			})?;
			let class_instance = (class, instance);
			Account::<T, I>::insert(&beneficiary, &(class, instance), ());
			let (class, instance) = class_instance;

			Self::deposit_event(Event::Issued(class, instance, beneficiary));
			Ok(())
		}

		/// Destroy a single asset instance.
		///
		/// Origin must be Signed and the sender should be the Manager of the asset `id`.
		///
		/// - `class`: The class of the asset to be burned.
		/// - `instance`: The instance of the asset to be burned.
		/// - `check_owner`: If `Some` then the operation will fail with `WrongOwner` unless the
		///   asset is owned by this value.
		///
		/// Emits `Burned` with the actual amount burned.
		///
		/// Weight: `O(1)`
		/// Modes: `check_owner.is_some()`.
		#[pallet::weight(T::WeightInfo::burn())]
		pub(super) fn burn(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			check_owner: Option<<T::Lookup as StaticLookup>::Source>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let check_owner = check_owner.map(T::Lookup::lookup).transpose()?;

			let owner = Class::<T, I>::try_mutate(&class, |maybe_class_details| -> Result<T::AccountId, DispatchError> {
				let class_details = maybe_class_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				let mut details = Asset::<T, I>::get(&class, &instance)
					.ok_or(Error::<T, I>::Unknown)?;
				let is_permitted = class_details.admin == origin || details.owner == origin;
				ensure!(is_permitted, Error::<T, I>::NoPermission);
				ensure!(check_owner.map_or(true, |o| o == details.owner), Error::<T, I>::WrongOwner);
				Self::dead_instance(&mut details, class_details);
				Ok(details.owner)
			})?;

			Asset::<T, I>::remove(&class, &instance);
			let class_instance = (class, instance);
			Account::<T, I>::remove(&owner, &class_instance);
			let (class, instance) = class_instance;

			Self::deposit_event(Event::Burned(class, instance, owner));
			Ok(())
		}

		/// Move an asset from the sender account to another.
		///
		/// Origin must be Signed.
		///
		/// - `class`: The class of the asset to be transferred.
		/// - `instance`: The instance of the asset to be transferred.
		/// - `dest`: The account to be credited.
		///
		/// Emits `Transferred` with the asset which was transferred.
		///
		/// Weight: `O(1)`
		/// Modes: source == dest.
		#[pallet::weight(T::WeightInfo::transfer())]
		pub(super) fn transfer(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			dest: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			let mut details = Asset::<T, I>::get(&class, &instance).ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.owner == origin, Error::<T, I>::NoPermission);

			let class_instance = (class, instance);
			Account::<T, I>::remove(&origin, &(class_instance));
			Account::<T, I>::insert(&dest, &(class_instance), ());
			let (class, instance) = class_instance;
			details.owner = dest;
			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::Transferred(class, instance, origin, details.owner));

			Ok(())
		}
/*
		/// Move some assets from one account to another.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `class`: The identifier of the asset to have some amount transferred.
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
			#[pallet::compact] class: T::ClassId,
			source: <T::Lookup as StaticLookup>::Source,
			dest: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::InstanceId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let source = T::Lookup::lookup(source)?;
			let dest = T::Lookup::lookup(dest)?;

			let f = TransferFlags {
				keep_alive: false,
				best_effort: false,
				burn_dust: false
			};
			Self::do_transfer(id, &source, &dest, amount, Some(origin), f).map(|_| ())
		}

		/// Disallow further unprivileged transfers from an account.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `id`.
		///
		/// - `class`: The identifier of the asset to be frozen.
		/// - `who`: The account to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze())]
		pub(super) fn freeze(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			who: <T::Lookup as StaticLookup>::Source
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
			ensure!(&origin == &d.freezer, Error::<T, I>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(
				Account::<T, I>::contains_key(id, &who),
				Error::<T, I>::BalanceZero
			);

			Account::<T, I>::mutate(id, &who, |a| a.is_frozen = true);

			Self::deposit_event(Event::<T, I>::Frozen(id, who));
			Ok(())
		}

		/// Allow unprivileged transfers from an account again.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `class`: The identifier of the asset to be frozen.
		/// - `who`: The account to be unfrozen.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw())]
		pub(super) fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact]
			class: T::ClassId,
			who: <T::Lookup as StaticLookup>::Source
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let details = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
			ensure!(&origin == &details.admin, Error::<T, I>::NoPermission);
			let who = T::Lookup::lookup(who)?;
			ensure!(
				Account::<T, I>::contains_key(id, &who),
				Error::<T, I>::BalanceZero
			);

			Account::<T, I>::mutate(id, &who, |a| a.is_frozen = false);

			Self::deposit_event(Event::<T, I>::Thawed(id, who));
			Ok(())
		}

		/// Disallow further unprivileged transfers for the asset class.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `id`.
		///
		/// - `class`: The identifier of the asset to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze_asset())]
		pub(super) fn freeze_asset(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Asset::<T, I>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &d.freezer, Error::<T, I>::NoPermission);

				d.is_frozen = true;

				Self::deposit_event(Event::<T, I>::AssetFrozen(id));
				Ok(())
			})
		}

		/// Allow unprivileged transfers for the asset again.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `class`: The identifier of the asset to be frozen.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw_asset())]
		pub(super) fn thaw_asset(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Asset::<T, I>::try_mutate(id, |maybe_details| {
				let d = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &d.admin, Error::<T, I>::NoPermission);

				d.is_frozen = false;

				Self::deposit_event(Event::<T, I>::AssetThawed(id));
				Ok(())
			})
		}

		/// Change the Owner of an asset.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `id`.
		///
		/// - `class`: The identifier of the asset.
		/// - `owner`: The new Owner of this asset.
		///
		/// Emits `OwnerChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer_ownership())]
		pub(super) fn transfer_ownership(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			owner: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Asset::<T, I>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T, I>::NoPermission);
				if details.owner == owner {
					return Ok(());
				}

				let metadata_deposit = Metadata::<T, I>::get(id).deposit;
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
		/// - `class`: The identifier of the asset to be frozen.
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
			#[pallet::compact] class: T::ClassId,
			issuer: <T::Lookup as StaticLookup>::Source,
			admin: <T::Lookup as StaticLookup>::Source,
			freezer: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let issuer = T::Lookup::lookup(issuer)?;
			let admin = T::Lookup::lookup(admin)?;
			let freezer = T::Lookup::lookup(freezer)?;

			Asset::<T, I>::try_mutate(id, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T, I>::NoPermission);

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
		/// - `class`: The identifier of the asset to update.
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
			#[pallet::compact] class: T::ClassId,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);
			ensure!(symbol.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);

			let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
			ensure!(&origin == &d.owner, Error::<T, I>::NoPermission);

			Metadata::<T, I>::try_mutate_exists(id, |metadata| {
				ensure!(
					metadata.as_ref().map_or(true, |m| !m.is_frozen),
					Error::<T, I>::NoPermission
				);

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
		/// - `class`: The identifier of the asset to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::clear_metadata())]
		pub(super) fn clear_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
			ensure!(&origin == &d.owner, Error::<T, I>::NoPermission);

			Metadata::<T, I>::try_mutate_exists(id, |metadata| {
				let deposit = metadata.take().ok_or(Error::<T, I>::Unknown)?.deposit;
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
		/// - `class`: The identifier of the asset to update.
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
			#[pallet::compact] class: T::ClassId,
			name: Vec<u8>,
			symbol: Vec<u8>,
			decimals: u8,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);
			ensure!(symbol.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);

			ensure!(Asset::<T, I>::contains_key(id), Error::<T, I>::Unknown);
			Metadata::<T, I>::try_mutate_exists(id, |metadata| {
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
		/// - `class`: The identifier of the asset to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_clear_metadata())]
		pub(super) fn force_clear_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
			Metadata::<T, I>::try_mutate_exists(id, |metadata| {
				let deposit = metadata.take().ok_or(Error::<T, I>::Unknown)?.deposit;
				T::Currency::unreserve(&d.owner, deposit);
				Self::deposit_event(Event::MetadataCleared(id));
				Ok(())
			})
		}

		/// Alter the attributes of a given asset.
		///
		/// Origin must be `ForceOrigin`.
		///
		/// - `class`: The identifier of the asset.
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
			#[pallet::compact] class: T::ClassId,
			owner: <T::Lookup as StaticLookup>::Source,
			issuer: <T::Lookup as StaticLookup>::Source,
			admin: <T::Lookup as StaticLookup>::Source,
			freezer: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] min_balance: T::InstanceId,
			is_sufficient: bool,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			Asset::<T, I>::try_mutate(id, |maybe_asset| {
				let mut asset = maybe_asset.take().ok_or(Error::<T, I>::Unknown)?;
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
		}*/
/*
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
		/// - `class`: The identifier of the asset.
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
			#[pallet::compact] class: T::ClassId,
			delegate: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::InstanceId,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;

			let key = ApprovalKey { owner, delegate };
			Approvals::<T, I>::try_mutate(id, &key, |maybe_approved| -> DispatchResult {
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
		/// - `class`: The identifier of the asset.
		/// - `delegate`: The account delegated permission to transfer asset.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::cancel_approval())]
		pub(super) fn cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let owner = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			let key = ApprovalKey { owner, delegate };
			let approval = Approvals::<T, I>::take(id, &key).ok_or(Error::<T, I>::Unknown)?;
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
		/// - `class`: The identifier of the asset.
		/// - `delegate`: The account delegated permission to transfer asset.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_cancel_approval())]
		pub(super) fn force_cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			owner: <T::Lookup as StaticLookup>::Source,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::ForceOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(|origin| -> DispatchResult {
					let origin = ensure_signed(origin)?;
					let d = Asset::<T, I>::get(id).ok_or(Error::<T, I>::Unknown)?;
					ensure!(&origin == &d.admin, Error::<T, I>::NoPermission);
					Ok(())
				})?;

			let owner = T::Lookup::lookup(owner)?;
			let delegate = T::Lookup::lookup(delegate)?;

			let key = ApprovalKey { owner, delegate };
			let approval = Approvals::<T, I>::take(id, &key).ok_or(Error::<T, I>::Unknown)?;
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
		/// - `class`: The identifier of the asset.
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
			#[pallet::compact] class: T::ClassId,
			owner: <T::Lookup as StaticLookup>::Source,
			destination: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] amount: T::InstanceId,
		) -> DispatchResult {
			let delegate = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;
			let destination = T::Lookup::lookup(destination)?;

			let key = ApprovalKey { owner, delegate };
			Approvals::<T, I>::try_mutate_exists(id, &key, |maybe_approved| -> DispatchResult {
				let mut approved = maybe_approved.take().ok_or(Error::<T, I>::Unapproved)?;
				let remaining = approved
					.amount
					.checked_sub(&amount)
					.ok_or(Error::<T, I>::Unapproved)?;

				let f = TransferFlags {
					keep_alive: false,
					best_effort: false,
					burn_dust: false
				};
				Self::do_transfer(id, &key.owner, &destination, amount, None, f)?;

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
 */
	}
}
