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
use frame_support::traits::{Currency, ReservableCurrency, BalanceStatus::Reserved};
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
		/// Some account `who` was frozen. \[ class, instance \]
		Frozen(T::ClassId, T::InstanceId),
		/// Some account `who` was thawed. \[ class, instance \]
		Thawed(T::ClassId, T::InstanceId),
		/// Some asset `class` was frozen. \[ class \]
		ClassFrozen(T::ClassId),
		/// Some asset `class` was thawed. \[ class \]
		ClassThawed(T::ClassId),
		/// The owner changed \[ class, owner \]
		OwnerChanged(T::ClassId, T::AccountId),
		/// The management team changed \[ class, issuer, admin, freezer \]
		TeamChanged(T::ClassId, T::AccountId, T::AccountId, T::AccountId),
		/// An `instance` of an asset `class` has been approved by the `owner` for transfer by a
		/// `delegate`.
		/// \[ clsss, instance, owner, delegate \]
		ApprovedTransfer(T::ClassId, T::InstanceId, T::AccountId, T::AccountId),
		/// An approval for a `delegate` account to transfer the `instance` of an asset `class` was
		/// cancelled by its `owner`.
		/// \[ clsss, instance, owner, delegate \]
		ApprovalCancelled(T::ClassId, T::InstanceId, T::AccountId, T::AccountId),
		/// The `instance` of the asset `class` was transferred from `owner` to `destination` by
		/// the approved `delegate`.
		/// \[ class, instance, owner, delegate, destination \]
		TransferredApproved(T::ClassId, T::InstanceId, T::AccountId, T::AccountId, T::AccountId),
		/// An asset `class` has had its attributes changed by the `Force` origin.
		/// \[ class \]
		AssetStatusChanged(T::ClassId),
		/// New metadata has been set for an asset class. \[ asset_id, name, is_frozen \]
		ClassMetadataSet(T::ClassId, Vec<u8>, bool),
		/// Metadata has been cleared for an asset class. \[ asset_id \]
		ClassMetadataCleared(T::ClassId),
		/// New metadata has been set for an asset instance. \[ asset_id, name, info, is_frozen \]
		MetadataSet(T::ClassId, Vec<u8>, Vec<u8>, bool),
		/// Metadata has been cleared for an asset instance. \[ asset_id \]
		MetadataCleared(T::ClassId),
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
		/// The asset instance or class is frozen.
		Frozen,
		/// The delegate turned out to be different to what was expected.
		WrongDelegate,
		/// There is no delegate approved.
		NoDelegate,
		/// No approval exists that would allow the transfer.
		Unapproved,
		/// Invalid metadata given.
		BadMetadata,
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
			Account::<T, I>::insert(&beneficiary, (&class, &instance), ());

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
			Account::<T, I>::remove(&owner, (&class, &instance));

			Self::deposit_event(Event::Burned(class, instance, owner));
			Ok(())
		}

		/// Move an asset from the sender account to another.
		///
		/// Origin must be Signed and the signing account must be the owner of the asset instance..
		///
		/// - `class`: The class of the asset to be transferred.
		/// - `instance`: The instance of the asset to be transferred.
		/// - `dest`: The account to receive ownership of the asset.
		///
		/// Emits `Transferred`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer())]
		pub(super) fn transfer(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			dest: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			ensure!(!class_details.is_frozen, Error::<T, I>::Frozen);

			let mut details = Asset::<T, I>::get(&class, &instance).ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.owner == origin, Error::<T, I>::NoPermission);
			ensure!(!details.is_frozen, Error::<T, I>::Frozen);

			Account::<T, I>::remove(&origin, (&class, &instance));
			Account::<T, I>::insert(&dest, (&class, &instance), ());
			details.owner = dest;
			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::Transferred(class, instance, origin, details.owner));

			Ok(())
		}

		/// Move some assets from one account to another.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `id`.
		///
		/// - `class`: The class of the asset to be transferred.
		/// - `instance`: The instance of the asset to be transferred.
		/// - `dest`: The account to receive ownership of the asset.
		///
		/// Emits `Transferred`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_transfer())]
		pub(super) fn force_transfer(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			dest: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			let mut details = Asset::<T, I>::get(&class, &instance).ok_or(Error::<T, I>::Unknown)?;
			let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			ensure!(class_details.admin == origin, Error::<T, I>::NoPermission);

			let source = details.owner;
			details.owner = dest;

			Account::<T, I>::remove(&source, (&class, &instance));
			Account::<T, I>::insert(&details.owner, (&class, &instance), ());

			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::Transferred(class, instance, source, details.owner));

			Ok(())
		}

		/// Disallow further unprivileged transfer of an asset instance.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `class`.
		///
		/// - `class`: The class of the asset to be frozen.
		/// - `instance`: The instance of the asset to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze())]
		pub(super) fn freeze(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let mut details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			ensure!(class_details.freezer == origin, Error::<T, I>::NoPermission);

			details.is_frozen = true;
			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::<T, I>::Frozen(class, instance));
			Ok(())
		}

		/// Allow unprivileged transfer of an asset instance.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `class`.
		///
		/// - `class`: The class of the asset to be thawed.
		/// - `instance`: The instance of the asset to be thawed.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw())]
		pub(super) fn thaw(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let mut details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			ensure!(class_details.admin == origin, Error::<T, I>::NoPermission);

			details.is_frozen = false;
			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::<T, I>::Frozen(class, instance));
			Ok(())
		}

		/// Disallow further unprivileged transfers for the asset class.
		///
		/// Origin must be Signed and the sender should be the Freezer of the asset `class`.
		///
		/// - `class`: The asset class to be frozen.
		///
		/// Emits `ClassFrozen`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::freeze_class())]
		pub(super) fn freeze_class(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Class::<T, I>::try_mutate(class, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.freezer, Error::<T, I>::NoPermission);

				details.is_frozen = true;

				Self::deposit_event(Event::<T, I>::ClassFrozen(class));
				Ok(())
			})
		}

		/// Allow unprivileged transfers for the asset again.
		///
		/// Origin must be Signed and the sender should be the Admin of the asset `class`.
		///
		/// - `class`: The class to be thawed.
		///
		/// Emits `ClassThawed`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::thaw_class())]
		pub(super) fn thaw_class(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Class::<T, I>::try_mutate(class, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.admin, Error::<T, I>::NoPermission);

				details.is_frozen = false;

				Self::deposit_event(Event::<T, I>::ClassThawed(class));
				Ok(())
			})
		}

		/// Change the Owner of an asset class.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `class`.
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

			Class::<T, I>::try_mutate(class, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T, I>::NoPermission);
				if details.owner == owner {
					return Ok(());
				}

				let metadata_deposit = ClassMetadataOf::<T, I>::get(class).deposit;
				let deposit = details.deposit + metadata_deposit;

				// Move the deposit to the new owner.
				T::Currency::repatriate_reserved(&details.owner, &owner, deposit, Reserved)?;

				details.owner = owner.clone();

				Self::deposit_event(Event::OwnerChanged(class, owner));
				Ok(())
			})
		}

		/// Change the Issuer, Admin and Freezer of an asset class.
		///
		/// Origin must be Signed and the sender should be the Owner of the asset `class`.
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

			Class::<T, I>::try_mutate(class, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::Unknown)?;
				ensure!(&origin == &details.owner, Error::<T, I>::NoPermission);

				details.issuer = issuer.clone();
				details.admin = admin.clone();
				details.freezer = freezer.clone();

				Self::deposit_event(Event::TeamChanged(class, issuer, admin, freezer));
				Ok(())
			})
		}

		/// Approve an instance to be transferred by a delegated third-party account.
		///
		/// Origin must be Signed and must be the owner of the asset `instance`.
		///
		/// - `class`: The class of the asset to be approved for transfer.
		/// - `instance`: The instance of the asset to be approved for transfer.
		/// - `delegate`: The account to delegate permission to transfer asset.
		///
		/// Emits `ApprovedTransfer` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::approve_transfer())]
		pub(super) fn approve_transfer(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;

			let mut details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.owner == origin, Error::<T, I>::NoPermission);

			details.approved = Some(delegate);
			Asset::<T, I>::insert(&class, &instance, &details);

			let delegate = details.approved.expect("set as Some above; qed");
			Self::deposit_event(Event::ApprovedTransfer(class, instance, origin, delegate));

			Ok(())
		}

		/// Cancel the prior approval for the transfer of an asset by a delegate.
		///
		/// Origin must be Signed and there must be an approval in place between signer and
		/// `delegate`.
		///
		/// - `class`: The class of the asset of whose approval will be cancelled.
		/// - `instance`: The instance of the asset of whose approval will be cancelled.
		/// - `maybe_check_delegate`: If `Some` will ensure that the given account is the one to
		///   which permission of transfer is delegated.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::cancel_approval())]
		pub(super) fn cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			maybe_check_delegate: Option<<T::Lookup as StaticLookup>::Source>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let maybe_check_delegate = maybe_check_delegate.map(T::Lookup::lookup).transpose()?;

			let mut details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			ensure!(details.owner == origin, Error::<T, I>::NoPermission);
			let old = details.approved.take().ok_or(Error::<T, I>::NoDelegate)?;
			if let Some(check_delegate) = maybe_check_delegate {
				ensure!(check_delegate == old, Error::<T, I>::WrongDelegate);
			}

			Asset::<T, I>::insert(&class, &instance, &details);
			Self::deposit_event(Event::ApprovalCancelled(class, instance, origin, old));

			Ok(())
		}

		/// Cancel the prior approval for the transfer of an asset by a delegate.
		///
		/// Origin must be either ForceOrigin or Signed origin with the signer being the Admin
		/// account of the asset `class`.
		///
		/// - `class`: The class of the asset of whose approval will be cancelled.
		/// - `instance`: The instance of the asset of whose approval will be cancelled.
		/// - `maybe_check_delegate`: If `Some` will ensure that the given account is the one to
		///   which permission of transfer is delegated.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_cancel_approval())]
		pub(super) fn force_cancel_approval(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			maybe_check_delegate: Option<<T::Lookup as StaticLookup>::Source>,
		) -> DispatchResult {
			T::ForceOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(|origin| -> DispatchResult {
					let origin = ensure_signed(origin)?;
					let d = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
					ensure!(&origin == &d.admin, Error::<T, I>::NoPermission);
					Ok(())
				})?;

			let maybe_check_delegate = maybe_check_delegate.map(T::Lookup::lookup).transpose()?;

			let mut details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			let old = details.approved.take().ok_or(Error::<T, I>::NoDelegate)?;
			if let Some(check_delegate) = maybe_check_delegate {
				ensure!(check_delegate == old, Error::<T, I>::WrongDelegate);
			}

			Asset::<T, I>::insert(&class, &instance, &details);
			Self::deposit_event(Event::ApprovalCancelled(class, instance, details.owner, old));

			Ok(())
		}

		/// Transfer some asset instance from a target account to a destination account by an
		/// approved delegate.
		///
		/// Origin must be Signed and there must be an approval in place by the `owner` to the
		/// signer.
		///
		/// - `class`: The class of the asset to transfer.
		/// - `instance`: The instance of the asset to transfer.
		/// - `dest`: The account to which ownership of the asset instance will be transferred.
		///
		/// Emits `TransferredApproved` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer_approved())]
		pub(super) fn transfer_approved(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			dest: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			let mut details = Asset::<T, I>::get(&class, &instance).ok_or(Error::<T, I>::Unknown)?;
			ensure!(!details.is_frozen, Error::<T, I>::Frozen);
			let class_details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			ensure!(!class_details.is_frozen, Error::<T, I>::Frozen);
			ensure!(details.approved.as_ref() == Some(&origin), Error::<T, I>::Unapproved);

			let source = details.owner;
			details.owner = dest;

			Account::<T, I>::remove(&source, (&class, &instance));
			Account::<T, I>::insert(&details.owner, (&class, &instance), ());

			Asset::<T, I>::insert(&class, &instance, &details);

			Self::deposit_event(Event::TransferredApproved(class, instance, source, origin, details.owner));

			Ok(())
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
			free_holding: bool,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			Class::<T, I>::try_mutate(class, |maybe_asset| {
				let mut asset = maybe_asset.take().ok_or(Error::<T, I>::Unknown)?;
				asset.owner = T::Lookup::lookup(owner)?;
				asset.issuer = T::Lookup::lookup(issuer)?;
				asset.admin = T::Lookup::lookup(admin)?;
				asset.freezer = T::Lookup::lookup(freezer)?;
				asset.free_holding = free_holding;
				asset.is_frozen = is_frozen;
				*maybe_asset = Some(asset);

				Self::deposit_event(Event::AssetStatusChanged(class));
				Ok(())
			})
		}

		/// Set the metadata for an asset instance.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// asset `instance`.
		///
		/// Funds of sender are reserved according to the formula:
		/// `MetadataDepositBase + MetadataDepositPerByte * (name.len + symbol.len)` taking into
		/// account any already reserved funds.
		///
		/// - `class`: The identifier of the asset class whose instance's metadata to clear.
		/// - `instance`: The identifier of the asset instance whose metadata to clear.
		/// - `name`: The user visible name of this asset. Limited in length by `StringLimit`.
		/// - `name`: The general information of this asset. Limited in length by `StringLimit`.
		/// - `is_frozen`: Whether the metadata should be frozen against further changes.
		///
		/// Emits `MetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_metadata(name.len() as u32, info.len() as u32))]
		pub(super) fn set_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
			name: Vec<u8>,
			info: Vec<u8>,
			is_frozen: bool,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);
			ensure!(info.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);

			if let Some(check_owner) = &maybe_check_owner {
				let details = Asset::<T, I>::get(&class, &instance)
					.ok_or(Error::<T, I>::Unknown)?;
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			InstanceMetadataOf::<T, I>::try_mutate_exists(class, instance, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				let deposit = if let Some(owner) = maybe_check_owner {
					let deposit = T::MetadataDepositPerByte::get()
						.saturating_mul((name.len() as u32).into())
						.saturating_add(T::MetadataDepositBase::get());

					if deposit > old_deposit {
						T::Currency::reserve(&owner, deposit - old_deposit)?;
					} else {
						T::Currency::unreserve(&owner, old_deposit - deposit);
					}
					deposit
				} else {
					old_deposit
				};

				*metadata = Some(InstanceMetadata {
					deposit,
					name: name.clone(),
					information: info.clone(),
					is_frozen,
				});

				Self::deposit_event(Event::MetadataSet(class, name, info, false));
				Ok(())
			})
		}

		/// Clear the metadata for an asset instance.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// asset `instance`.
		///
		/// Any deposit is freed for the asset class owner.
		///
		/// - `class`: The identifier of the asset class whose instance's metadata to clear.
		/// - `instance`: The identifier of the asset instance whose metadata to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::clear_metadata())]
		pub(super) fn clear_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			#[pallet::compact] instance: T::InstanceId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let details = Asset::<T, I>::get(&class, &instance)
				.ok_or(Error::<T, I>::Unknown)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			InstanceMetadataOf::<T, I>::try_mutate_exists(class, instance, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let deposit = metadata.take().ok_or(Error::<T, I>::Unknown)?.deposit;
				T::Currency::unreserve(&details.owner, deposit);
				Self::deposit_event(Event::MetadataCleared(class));
				Ok(())
			})
		}

		/// Set the metadata for an asset class.
		///
		/// Origin must be either `ForceOrigin` or `Signed` and the sender should be the Owner of
		/// the asset `class`.
		///
		/// Funds of sender are reserved according to the formula:
		/// `MetadataDepositBase + MetadataDepositPerByte * (name.len + symbol.len)` taking into
		/// account any already reserved funds.
		///
		/// - `class`: The identifier of the asset to update.
		/// - `name`: The user visible name of this asset. Limited in length by `StringLimit`.
		/// - `is_frozen`: Whether the metadata should be frozen against further changes.
		///
		/// Emits `ClassMetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_class_metadata(name.len() as u32))]
		pub(super) fn set_class_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
			name: Vec<u8>,
			is_frozen: bool,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			ensure!(name.len() <= T::StringLimit::get() as usize, Error::<T, I>::BadMetadata);

			if let Some(check_owner) = &maybe_check_owner {
				let details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			ClassMetadataOf::<T, I>::try_mutate_exists(class, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				let deposit = if let Some(owner) = maybe_check_owner {
					let deposit = T::MetadataDepositPerByte::get()
						.saturating_mul((name.len() as u32).into())
						.saturating_add(T::MetadataDepositBase::get());

					if deposit > old_deposit {
						T::Currency::reserve(&owner, deposit - old_deposit)?;
					} else {
						T::Currency::unreserve(&owner, old_deposit - deposit);
					}
					deposit
				} else {
					old_deposit
				};

				*metadata = Some(ClassMetadata {
					deposit,
					name: name.clone(),
					is_frozen,
				});

				Self::deposit_event(Event::ClassMetadataSet(class, name, false));
				Ok(())
			})
		}

		/// Clear the metadata for an asset class.
		///
		/// Origin must be either `ForceOrigin` or `Signed` and the sender should be the Owner of
		/// the asset `class`.
		///
		/// Any deposit is freed for the asset class owner.
		///
		/// - `class`: The identifier of the asset class whose metadata to clear.
		///
		/// Emits `ClassMetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::clear_class_metadata())]
		pub(super) fn clear_class_metadata(
			origin: OriginFor<T>,
			#[pallet::compact] class: T::ClassId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let details = Class::<T, I>::get(&class).ok_or(Error::<T, I>::Unknown)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			ClassMetadataOf::<T, I>::try_mutate_exists(class, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let deposit = metadata.take().ok_or(Error::<T, I>::Unknown)?.deposit;
				T::Currency::unreserve(&details.owner, deposit);
				Self::deposit_event(Event::ClassMetadataCleared(class));
				Ok(())
			})
		}
	}
}
