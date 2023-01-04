// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Unique (Items) Module
//!
//! A simple, secure module for dealing with non-fungible items.
//!
//! ## Related Modules
//!
//! * [`System`](../frame_system/index.html)
//! * [`Support`](../frame_support/index.html)

#![recursion_limit = "256"]
// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;

mod functions;
mod impl_nonfungibles;
mod types;

pub mod migration;
pub mod weights;

use codec::{Decode, Encode};
use frame_support::{
	traits::{
		tokens::Locker, BalanceStatus::Reserved, Currency, EnsureOriginWithArg, ReservableCurrency,
	},
	transactional,
};
use frame_system::Config as SystemConfig;
use sp_runtime::{
	traits::{Saturating, StaticLookup, Zero},
	ArithmeticError, RuntimeDebug,
};
use sp_std::prelude::*;

pub use pallet::*;
pub use types::*;
pub use weights::WeightInfo;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(_);

	#[cfg(feature = "runtime-benchmarks")]
	pub trait BenchmarkHelper<CollectionId, ItemId> {
		fn collection(i: u16) -> CollectionId;
		fn item(i: u16) -> ItemId;
	}
	#[cfg(feature = "runtime-benchmarks")]
	impl<CollectionId: From<u16>, ItemId: From<u16>> BenchmarkHelper<CollectionId, ItemId> for () {
		fn collection(i: u16) -> CollectionId {
			i.into()
		}
		fn item(i: u16) -> ItemId {
			i.into()
		}
	}

	#[pallet::config]
	/// The module configuration trait.
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Identifier for the collection of item.
		type CollectionId: Member + Parameter + MaxEncodedLen + Copy;

		/// The type used to identify a unique item within a collection.
		type ItemId: Member + Parameter + MaxEncodedLen + Copy;

		/// The currency mechanism, used for paying for reserves.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The origin which may forcibly create or destroy an item or otherwise alter privileged
		/// attributes.
		type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Standard collection creation is only allowed if the origin attempting it and the
		/// collection are in this set.
		type CreateOrigin: EnsureOriginWithArg<
			Self::RuntimeOrigin,
			Self::CollectionId,
			Success = Self::AccountId,
		>;

		/// Locker trait to enable Locking mechanism downstream.
		type Locker: Locker<Self::CollectionId, Self::ItemId>;

		/// The basic amount of funds that must be reserved for collection.
		#[pallet::constant]
		type CollectionDeposit: Get<DepositBalanceOf<Self, I>>;

		/// The basic amount of funds that must be reserved for an item.
		#[pallet::constant]
		type ItemDeposit: Get<DepositBalanceOf<Self, I>>;

		/// The basic amount of funds that must be reserved when adding metadata to your item.
		#[pallet::constant]
		type MetadataDepositBase: Get<DepositBalanceOf<Self, I>>;

		/// The basic amount of funds that must be reserved when adding an attribute to an item.
		#[pallet::constant]
		type AttributeDepositBase: Get<DepositBalanceOf<Self, I>>;

		/// The additional funds that must be reserved for the number of bytes store in metadata,
		/// either "normal" metadata or attribute metadata.
		#[pallet::constant]
		type DepositPerByte: Get<DepositBalanceOf<Self, I>>;

		/// The maximum length of data stored on-chain.
		#[pallet::constant]
		type StringLimit: Get<u32>;

		/// The maximum length of an attribute key.
		#[pallet::constant]
		type KeyLimit: Get<u32>;

		/// The maximum length of an attribute value.
		#[pallet::constant]
		type ValueLimit: Get<u32>;

		#[cfg(feature = "runtime-benchmarks")]
		/// A set of helper functions for benchmarking.
		type Helper: BenchmarkHelper<Self::CollectionId, Self::ItemId>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::storage]
	#[pallet::storage_prefix = "Class"]
	/// Details of a collection.
	pub(super) type Collection<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionDetails<T::AccountId, DepositBalanceOf<T, I>>,
	>;

	#[pallet::storage]
	/// The collection, if any, of which an account is willing to take ownership.
	pub(super) type OwnershipAcceptance<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, T::CollectionId>;

	#[pallet::storage]
	/// The items held by any given account; set out this way so that items owned by a single
	/// account can be enumerated.
	pub(super) type Account<T: Config<I>, I: 'static = ()> = StorageNMap<
		_,
		(
			NMapKey<Blake2_128Concat, T::AccountId>, // owner
			NMapKey<Blake2_128Concat, T::CollectionId>,
			NMapKey<Blake2_128Concat, T::ItemId>,
		),
		(),
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::storage_prefix = "ClassAccount"]
	/// The collections owned by any given account; set out this way so that collections owned by
	/// a single account can be enumerated.
	pub(super) type CollectionAccount<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		T::CollectionId,
		(),
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::storage_prefix = "Asset"]
	/// The items in existence and their ownership details.
	pub(super) type Item<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemDetails<T::AccountId, DepositBalanceOf<T, I>>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::storage_prefix = "ClassMetadataOf"]
	/// Metadata of a collection.
	pub(super) type CollectionMetadataOf<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionMetadata<DepositBalanceOf<T, I>, T::StringLimit>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::storage_prefix = "InstanceMetadataOf"]
	/// Metadata of an item.
	pub(super) type ItemMetadataOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemMetadata<DepositBalanceOf<T, I>, T::StringLimit>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Attributes of a collection.
	pub(super) type Attribute<T: Config<I>, I: 'static = ()> = StorageNMap<
		_,
		(
			NMapKey<Blake2_128Concat, T::CollectionId>,
			NMapKey<Blake2_128Concat, Option<T::ItemId>>,
			NMapKey<Blake2_128Concat, BoundedVec<u8, T::KeyLimit>>,
		),
		(BoundedVec<u8, T::ValueLimit>, DepositBalanceOf<T, I>),
		OptionQuery,
	>;

	#[pallet::storage]
	/// Price of an asset instance.
	pub(super) type ItemPriceOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		(ItemPrice<T, I>, Option<T::AccountId>),
		OptionQuery,
	>;

	#[pallet::storage]
	/// Keeps track of the number of items a collection might have.
	pub(super) type CollectionMaxSupply<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::CollectionId, u32, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A `collection` was created.
		Created { collection: T::CollectionId, creator: T::AccountId, owner: T::AccountId },
		/// A `collection` was force-created.
		ForceCreated { collection: T::CollectionId, owner: T::AccountId },
		/// A `collection` was destroyed.
		Destroyed { collection: T::CollectionId },
		/// An `item` was issued.
		Issued { collection: T::CollectionId, item: T::ItemId, owner: T::AccountId },
		/// An `item` was transferred.
		Transferred {
			collection: T::CollectionId,
			item: T::ItemId,
			from: T::AccountId,
			to: T::AccountId,
		},
		/// An `item` was destroyed.
		Burned { collection: T::CollectionId, item: T::ItemId, owner: T::AccountId },
		/// Some `item` was frozen.
		Frozen { collection: T::CollectionId, item: T::ItemId },
		/// Some `item` was thawed.
		Thawed { collection: T::CollectionId, item: T::ItemId },
		/// Some `collection` was frozen.
		CollectionFrozen { collection: T::CollectionId },
		/// Some `collection` was thawed.
		CollectionThawed { collection: T::CollectionId },
		/// The owner changed.
		OwnerChanged { collection: T::CollectionId, new_owner: T::AccountId },
		/// The management team changed.
		TeamChanged {
			collection: T::CollectionId,
			issuer: T::AccountId,
			admin: T::AccountId,
			freezer: T::AccountId,
		},
		/// An `item` of a `collection` has been approved by the `owner` for transfer by
		/// a `delegate`.
		ApprovedTransfer {
			collection: T::CollectionId,
			item: T::ItemId,
			owner: T::AccountId,
			delegate: T::AccountId,
		},
		/// An approval for a `delegate` account to transfer the `item` of an item
		/// `collection` was cancelled by its `owner`.
		ApprovalCancelled {
			collection: T::CollectionId,
			item: T::ItemId,
			owner: T::AccountId,
			delegate: T::AccountId,
		},
		/// A `collection` has had its attributes changed by the `Force` origin.
		ItemStatusChanged { collection: T::CollectionId },
		/// New metadata has been set for a `collection`.
		CollectionMetadataSet {
			collection: T::CollectionId,
			data: BoundedVec<u8, T::StringLimit>,
			is_frozen: bool,
		},
		/// Metadata has been cleared for a `collection`.
		CollectionMetadataCleared { collection: T::CollectionId },
		/// New metadata has been set for an item.
		MetadataSet {
			collection: T::CollectionId,
			item: T::ItemId,
			data: BoundedVec<u8, T::StringLimit>,
			is_frozen: bool,
		},
		/// Metadata has been cleared for an item.
		MetadataCleared { collection: T::CollectionId, item: T::ItemId },
		/// Metadata has been cleared for an item.
		Redeposited { collection: T::CollectionId, successful_items: Vec<T::ItemId> },
		/// New attribute metadata has been set for a `collection` or `item`.
		AttributeSet {
			collection: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: BoundedVec<u8, T::KeyLimit>,
			value: BoundedVec<u8, T::ValueLimit>,
		},
		/// Attribute metadata has been cleared for a `collection` or `item`.
		AttributeCleared {
			collection: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: BoundedVec<u8, T::KeyLimit>,
		},
		/// Ownership acceptance has changed for an account.
		OwnershipAcceptanceChanged { who: T::AccountId, maybe_collection: Option<T::CollectionId> },
		/// Max supply has been set for a collection.
		CollectionMaxSupplySet { collection: T::CollectionId, max_supply: u32 },
		/// The price was set for the instance.
		ItemPriceSet {
			collection: T::CollectionId,
			item: T::ItemId,
			price: ItemPrice<T, I>,
			whitelisted_buyer: Option<T::AccountId>,
		},
		/// The price for the instance was removed.
		ItemPriceRemoved { collection: T::CollectionId, item: T::ItemId },
		/// An item was bought.
		ItemBought {
			collection: T::CollectionId,
			item: T::ItemId,
			price: ItemPrice<T, I>,
			seller: T::AccountId,
			buyer: T::AccountId,
		},
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// The given item ID is unknown.
		UnknownCollection,
		/// The item ID has already been used for an item.
		AlreadyExists,
		/// The owner turned out to be different to what was expected.
		WrongOwner,
		/// Invalid witness data given.
		BadWitness,
		/// The item ID is already taken.
		InUse,
		/// The item or collection is frozen.
		Frozen,
		/// The delegate turned out to be different to what was expected.
		WrongDelegate,
		/// There is no delegate approved.
		NoDelegate,
		/// No approval exists that would allow the transfer.
		Unapproved,
		/// The named owner has not signed ownership of the collection is acceptable.
		Unaccepted,
		/// The item is locked.
		Locked,
		/// All items have been minted.
		MaxSupplyReached,
		/// The max supply has already been set.
		MaxSupplyAlreadySet,
		/// The provided max supply is less to the amount of items a collection already has.
		MaxSupplyTooSmall,
		/// The given item ID is unknown.
		UnknownItem,
		/// Item is not for sale.
		NotForSale,
		/// The provided bid is too low.
		BidTooLow,
	}

	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Get the owner of the item, if the item exists.
		pub fn owner(collection: T::CollectionId, item: T::ItemId) -> Option<T::AccountId> {
			Item::<T, I>::get(collection, item).map(|i| i.owner)
		}

		/// Get the owner of the item, if the item exists.
		pub fn collection_owner(collection: T::CollectionId) -> Option<T::AccountId> {
			Collection::<T, I>::get(collection).map(|i| i.owner)
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Issue a new collection of non-fungible items from a public origin.
		///
		/// This new collection has no items initially and its owner is the origin.
		///
		/// The origin must conform to the configured `CreateOrigin` and have sufficient funds free.
		///
		/// `ItemDeposit` funds of sender are reserved.
		///
		/// Parameters:
		/// - `collection`: The identifier of the new collection. This must not be currently in use.
		/// - `admin`: The admin of this collection. The admin is the initial address of each
		/// member of the collection's admin team.
		///
		/// Emits `Created` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::create())]
		pub fn create(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			admin: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let owner = T::CreateOrigin::ensure_origin(origin, &collection)?;
			let admin = T::Lookup::lookup(admin)?;

			Self::do_create_collection(
				collection,
				owner.clone(),
				admin.clone(),
				T::CollectionDeposit::get(),
				false,
				Event::Created { collection, creator: owner, owner: admin },
			)
		}

		/// Issue a new collection of non-fungible items from a privileged origin.
		///
		/// This new collection has no items initially.
		///
		/// The origin must conform to `ForceOrigin`.
		///
		/// Unlike `create`, no funds are reserved.
		///
		/// - `collection`: The identifier of the new item. This must not be currently in use.
		/// - `owner`: The owner of this collection of items. The owner has full superuser
		///   permissions
		/// over this item, but may later change and configure the permissions using
		/// `transfer_ownership` and `set_team`.
		///
		/// Emits `ForceCreated` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::force_create())]
		pub fn force_create(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			owner: AccountIdLookupOf<T>,
			free_holding: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Self::do_create_collection(
				collection,
				owner.clone(),
				owner.clone(),
				Zero::zero(),
				free_holding,
				Event::ForceCreated { collection, owner },
			)
		}

		/// Destroy a collection of fungible items.
		///
		/// The origin must conform to `ForceOrigin` or must be `Signed` and the sender must be the
		/// owner of the `collection`.
		///
		/// - `collection`: The identifier of the collection to be destroyed.
		/// - `witness`: Information on the items minted in the collection. This must be
		/// correct.
		///
		/// Emits `Destroyed` event when successful.
		///
		/// Weight: `O(n + m)` where:
		/// - `n = witness.items`
		/// - `m = witness.item_metadatas`
		/// - `a = witness.attributes`
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::destroy(
			witness.items,
 			witness.item_metadatas,
			witness.attributes,
 		))]
		pub fn destroy(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			witness: DestroyWitness,
		) -> DispatchResultWithPostInfo {
			let maybe_check_owner = match T::ForceOrigin::try_origin(origin) {
				Ok(_) => None,
				Err(origin) => Some(ensure_signed(origin)?),
			};
			let details = Self::do_destroy_collection(collection, witness, maybe_check_owner)?;

			Ok(Some(T::WeightInfo::destroy(
				details.items,
				details.item_metadatas,
				details.attributes,
			))
			.into())
		}

		/// Mint an item of a particular collection.
		///
		/// The origin must be Signed and the sender must be the Issuer of the `collection`.
		///
		/// - `collection`: The collection of the item to be minted.
		/// - `item`: The item value of the item to be minted.
		/// - `beneficiary`: The initial owner of the minted item.
		///
		/// Emits `Issued` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::mint())]
		pub fn mint(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			owner: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			Self::do_mint(collection, item, owner, |collection_details| {
				ensure!(collection_details.issuer == origin, Error::<T, I>::NoPermission);
				Ok(())
			})
		}

		/// Destroy a single item.
		///
		/// Origin must be Signed and the signing account must be either:
		/// - the Admin of the `collection`;
		/// - the Owner of the `item`;
		///
		/// - `collection`: The collection of the item to be burned.
		/// - `item`: The item of the item to be burned.
		/// - `check_owner`: If `Some` then the operation will fail with `WrongOwner` unless the
		///   item is owned by this value.
		///
		/// Emits `Burned` with the actual amount burned.
		///
		/// Weight: `O(1)`
		/// Modes: `check_owner.is_some()`.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::burn())]
		pub fn burn(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			check_owner: Option<AccountIdLookupOf<T>>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let check_owner = check_owner.map(T::Lookup::lookup).transpose()?;

			Self::do_burn(collection, item, |collection_details, details| {
				let is_permitted = collection_details.admin == origin || details.owner == origin;
				ensure!(is_permitted, Error::<T, I>::NoPermission);
				ensure!(
					check_owner.map_or(true, |o| o == details.owner),
					Error::<T, I>::WrongOwner
				);
				Ok(())
			})
		}

		/// Move an item from the sender account to another.
		///
		/// This resets the approved account of the item.
		///
		/// Origin must be Signed and the signing account must be either:
		/// - the Admin of the `collection`;
		/// - the Owner of the `item`;
		/// - the approved delegate for the `item` (in this case, the approval is reset).
		///
		/// Arguments:
		/// - `collection`: The collection of the item to be transferred.
		/// - `item`: The item of the item to be transferred.
		/// - `dest`: The account to receive ownership of the item.
		///
		/// Emits `Transferred`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::transfer())]
		pub fn transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			dest: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			Self::do_transfer(collection, item, dest, |collection_details, details| {
				if details.owner != origin && collection_details.admin != origin {
					let approved = details.approved.take().map_or(false, |i| i == origin);
					ensure!(approved, Error::<T, I>::NoPermission);
				}
				Ok(())
			})
		}

		/// Reevaluate the deposits on some items.
		///
		/// Origin must be Signed and the sender should be the Owner of the `collection`.
		///
		/// - `collection`: The collection to be frozen.
		/// - `items`: The items of the collection whose deposits will be reevaluated.
		///
		/// NOTE: This exists as a best-effort function. Any items which are unknown or
		/// in the case that the owner account does not have reservable funds to pay for a
		/// deposit increase are ignored. Generally the owner isn't going to call this on items
		/// whose existing deposit is less than the refreshed deposit as it would only cost them,
		/// so it's of little consequence.
		///
		/// It will still return an error in the case that the collection is unknown of the signer
		/// is not permitted to call it.
		///
		/// Weight: `O(items.len())`
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::redeposit(items.len() as u32))]
		pub fn redeposit(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			items: Vec<T::ItemId>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			ensure!(collection_details.owner == origin, Error::<T, I>::NoPermission);
			let deposit = match collection_details.free_holding {
				true => Zero::zero(),
				false => T::ItemDeposit::get(),
			};

			let mut successful = Vec::with_capacity(items.len());
			for item in items.into_iter() {
				let mut details = match Item::<T, I>::get(&collection, &item) {
					Some(x) => x,
					None => continue,
				};
				let old = details.deposit;
				if old > deposit {
					T::Currency::unreserve(&collection_details.owner, old - deposit);
				} else if deposit > old {
					if T::Currency::reserve(&collection_details.owner, deposit - old).is_err() {
						// NOTE: No alterations made to collection_details in this iteration so far,
						// so this is OK to do.
						continue
					}
				} else {
					continue
				}
				collection_details.total_deposit.saturating_accrue(deposit);
				collection_details.total_deposit.saturating_reduce(old);
				details.deposit = deposit;
				Item::<T, I>::insert(&collection, &item, &details);
				successful.push(item);
			}
			Collection::<T, I>::insert(&collection, &collection_details);

			Self::deposit_event(Event::<T, I>::Redeposited {
				collection,
				successful_items: successful,
			});

			Ok(())
		}

		/// Disallow further unprivileged transfer of an item.
		///
		/// Origin must be Signed and the sender should be the Freezer of the `collection`.
		///
		/// - `collection`: The collection of the item to be frozen.
		/// - `item`: The item of the item to be frozen.
		///
		/// Emits `Frozen`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::freeze())]
		pub fn freeze(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
			let collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			ensure!(collection_details.freezer == origin, Error::<T, I>::NoPermission);

			details.is_frozen = true;
			Item::<T, I>::insert(&collection, &item, &details);

			Self::deposit_event(Event::<T, I>::Frozen { collection, item });
			Ok(())
		}

		/// Re-allow unprivileged transfer of an item.
		///
		/// Origin must be Signed and the sender should be the Freezer of the `collection`.
		///
		/// - `collection`: The collection of the item to be thawed.
		/// - `item`: The item of the item to be thawed.
		///
		/// Emits `Thawed`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::thaw())]
		pub fn thaw(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
			let collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			ensure!(collection_details.admin == origin, Error::<T, I>::NoPermission);

			details.is_frozen = false;
			Item::<T, I>::insert(&collection, &item, &details);

			Self::deposit_event(Event::<T, I>::Thawed { collection, item });
			Ok(())
		}

		/// Disallow further unprivileged transfers for a whole collection.
		///
		/// Origin must be Signed and the sender should be the Freezer of the `collection`.
		///
		/// - `collection`: The collection to be frozen.
		///
		/// Emits `CollectionFrozen`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::freeze_collection())]
		pub fn freeze_collection(
			origin: OriginFor<T>,
			collection: T::CollectionId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Collection::<T, I>::try_mutate(collection, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				ensure!(origin == details.freezer, Error::<T, I>::NoPermission);

				details.is_frozen = true;

				Self::deposit_event(Event::<T, I>::CollectionFrozen { collection });
				Ok(())
			})
		}

		/// Re-allow unprivileged transfers for a whole collection.
		///
		/// Origin must be Signed and the sender should be the Admin of the `collection`.
		///
		/// - `collection`: The collection to be thawed.
		///
		/// Emits `CollectionThawed`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::thaw_collection())]
		pub fn thaw_collection(
			origin: OriginFor<T>,
			collection: T::CollectionId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			Collection::<T, I>::try_mutate(collection, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				ensure!(origin == details.admin, Error::<T, I>::NoPermission);

				details.is_frozen = false;

				Self::deposit_event(Event::<T, I>::CollectionThawed { collection });
				Ok(())
			})
		}

		/// Change the Owner of a collection.
		///
		/// Origin must be Signed and the sender should be the Owner of the `collection`.
		///
		/// - `collection`: The collection whose owner should be changed.
		/// - `owner`: The new Owner of this collection. They must have called
		///   `set_accept_ownership` with `collection` in order for this operation to succeed.
		///
		/// Emits `OwnerChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::transfer_ownership())]
		pub fn transfer_ownership(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			owner: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			let acceptable_collection = OwnershipAcceptance::<T, I>::get(&owner);
			ensure!(acceptable_collection.as_ref() == Some(&collection), Error::<T, I>::Unaccepted);

			Collection::<T, I>::try_mutate(collection, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				ensure!(origin == details.owner, Error::<T, I>::NoPermission);
				if details.owner == owner {
					return Ok(())
				}

				// Move the deposit to the new owner.
				T::Currency::repatriate_reserved(
					&details.owner,
					&owner,
					details.total_deposit,
					Reserved,
				)?;
				CollectionAccount::<T, I>::remove(&details.owner, &collection);
				CollectionAccount::<T, I>::insert(&owner, &collection, ());
				details.owner = owner.clone();
				OwnershipAcceptance::<T, I>::remove(&owner);

				Self::deposit_event(Event::OwnerChanged { collection, new_owner: owner });
				Ok(())
			})
		}

		/// Change the Issuer, Admin and Freezer of a collection.
		///
		/// Origin must be Signed and the sender should be the Owner of the `collection`.
		///
		/// - `collection`: The collection whose team should be changed.
		/// - `issuer`: The new Issuer of this collection.
		/// - `admin`: The new Admin of this collection.
		/// - `freezer`: The new Freezer of this collection.
		///
		/// Emits `TeamChanged`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::set_team())]
		pub fn set_team(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			issuer: AccountIdLookupOf<T>,
			admin: AccountIdLookupOf<T>,
			freezer: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let issuer = T::Lookup::lookup(issuer)?;
			let admin = T::Lookup::lookup(admin)?;
			let freezer = T::Lookup::lookup(freezer)?;

			Collection::<T, I>::try_mutate(collection, |maybe_details| {
				let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				ensure!(origin == details.owner, Error::<T, I>::NoPermission);

				details.issuer = issuer.clone();
				details.admin = admin.clone();
				details.freezer = freezer.clone();

				Self::deposit_event(Event::TeamChanged { collection, issuer, admin, freezer });
				Ok(())
			})
		}

		/// Approve an item to be transferred by a delegated third-party account.
		///
		/// The origin must conform to `ForceOrigin` or must be `Signed` and the sender must be
		/// either the owner of the `item` or the admin of the collection.
		///
		/// - `collection`: The collection of the item to be approved for delegated transfer.
		/// - `item`: The item of the item to be approved for delegated transfer.
		/// - `delegate`: The account to delegate permission to transfer the item.
		///
		/// Important NOTE: The `approved` account gets reset after each transfer.
		///
		/// Emits `ApprovedTransfer` on success.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::approve_transfer())]
		pub fn approve_transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			delegate: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let maybe_check: Option<T::AccountId> = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			let delegate = T::Lookup::lookup(delegate)?;

			let collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;

			if let Some(check) = maybe_check {
				let permitted = check == collection_details.admin || check == details.owner;
				ensure!(permitted, Error::<T, I>::NoPermission);
			}

			details.approved = Some(delegate);
			Item::<T, I>::insert(&collection, &item, &details);

			let delegate = details.approved.expect("set as Some above; qed");
			Self::deposit_event(Event::ApprovedTransfer {
				collection,
				item,
				owner: details.owner,
				delegate,
			});

			Ok(())
		}

		/// Cancel the prior approval for the transfer of an item by a delegate.
		///
		/// Origin must be either:
		/// - the `Force` origin;
		/// - `Signed` with the signer being the Admin of the `collection`;
		/// - `Signed` with the signer being the Owner of the `item`;
		///
		/// Arguments:
		/// - `collection`: The collection of the item of whose approval will be cancelled.
		/// - `item`: The item of the item of whose approval will be cancelled.
		/// - `maybe_check_delegate`: If `Some` will ensure that the given account is the one to
		///   which permission of transfer is delegated.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::cancel_approval())]
		pub fn cancel_approval(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			maybe_check_delegate: Option<AccountIdLookupOf<T>>,
		) -> DispatchResult {
			let maybe_check: Option<T::AccountId> = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			let collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check) = maybe_check {
				let permitted = check == collection_details.admin || check == details.owner;
				ensure!(permitted, Error::<T, I>::NoPermission);
			}
			let maybe_check_delegate = maybe_check_delegate.map(T::Lookup::lookup).transpose()?;
			let old = details.approved.take().ok_or(Error::<T, I>::NoDelegate)?;
			if let Some(check_delegate) = maybe_check_delegate {
				ensure!(check_delegate == old, Error::<T, I>::WrongDelegate);
			}

			Item::<T, I>::insert(&collection, &item, &details);
			Self::deposit_event(Event::ApprovalCancelled {
				collection,
				item,
				owner: details.owner,
				delegate: old,
			});

			Ok(())
		}

		/// Alter the attributes of a given item.
		///
		/// Origin must be `ForceOrigin`.
		///
		/// - `collection`: The identifier of the item.
		/// - `owner`: The new Owner of this item.
		/// - `issuer`: The new Issuer of this item.
		/// - `admin`: The new Admin of this item.
		/// - `freezer`: The new Freezer of this item.
		/// - `free_holding`: Whether a deposit is taken for holding an item of this collection.
		/// - `is_frozen`: Whether this collection is frozen except for permissioned/admin
		/// instructions.
		///
		/// Emits `ItemStatusChanged` with the identity of the item.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(15)]
		#[pallet::weight(T::WeightInfo::force_item_status())]
		pub fn force_item_status(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			owner: AccountIdLookupOf<T>,
			issuer: AccountIdLookupOf<T>,
			admin: AccountIdLookupOf<T>,
			freezer: AccountIdLookupOf<T>,
			free_holding: bool,
			is_frozen: bool,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			Collection::<T, I>::try_mutate(collection, |maybe_item| {
				let mut item = maybe_item.take().ok_or(Error::<T, I>::UnknownCollection)?;
				let old_owner = item.owner;
				let new_owner = T::Lookup::lookup(owner)?;
				item.owner = new_owner.clone();
				item.issuer = T::Lookup::lookup(issuer)?;
				item.admin = T::Lookup::lookup(admin)?;
				item.freezer = T::Lookup::lookup(freezer)?;
				item.free_holding = free_holding;
				item.is_frozen = is_frozen;
				*maybe_item = Some(item);
				CollectionAccount::<T, I>::remove(&old_owner, &collection);
				CollectionAccount::<T, I>::insert(&new_owner, &collection, ());

				Self::deposit_event(Event::ItemStatusChanged { collection });
				Ok(())
			})
		}

		/// Set an attribute for a collection or item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `collection`.
		///
		/// If the origin is Signed, then funds of signer are reserved according to the formula:
		/// `MetadataDepositBase + DepositPerByte * (key.len + value.len)` taking into
		/// account any already reserved funds.
		///
		/// - `collection`: The identifier of the collection whose item's metadata to set.
		/// - `maybe_item`: The identifier of the item whose metadata to set.
		/// - `key`: The key of the attribute.
		/// - `value`: The value to which to set the attribute.
		///
		/// Emits `AttributeSet`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(16)]
		#[pallet::weight(T::WeightInfo::set_attribute())]
		pub fn set_attribute(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: BoundedVec<u8, T::KeyLimit>,
			value: BoundedVec<u8, T::ValueLimit>,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}
			let maybe_is_frozen = match maybe_item {
				None => CollectionMetadataOf::<T, I>::get(collection).map(|v| v.is_frozen),
				Some(item) => ItemMetadataOf::<T, I>::get(collection, item).map(|v| v.is_frozen),
			};
			ensure!(!maybe_is_frozen.unwrap_or(false), Error::<T, I>::Frozen);

			let attribute = Attribute::<T, I>::get((collection, maybe_item, &key));
			if attribute.is_none() {
				collection_details.attributes.saturating_inc();
			}
			let old_deposit = attribute.map_or(Zero::zero(), |m| m.1);
			collection_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if !collection_details.free_holding && maybe_check_owner.is_some() {
				deposit = T::DepositPerByte::get()
					.saturating_mul(((key.len() + value.len()) as u32).into())
					.saturating_add(T::AttributeDepositBase::get());
			}
			collection_details.total_deposit.saturating_accrue(deposit);
			if deposit > old_deposit {
				T::Currency::reserve(&collection_details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&collection_details.owner, old_deposit - deposit);
			}

			Attribute::<T, I>::insert((&collection, maybe_item, &key), (&value, deposit));
			Collection::<T, I>::insert(collection, &collection_details);
			Self::deposit_event(Event::AttributeSet { collection, maybe_item, key, value });
			Ok(())
		}

		/// Clear an attribute for a collection or item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `collection`.
		///
		/// Any deposit is freed for the collection's owner.
		///
		/// - `collection`: The identifier of the collection whose item's metadata to clear.
		/// - `maybe_item`: The identifier of the item whose metadata to clear.
		/// - `key`: The key of the attribute.
		///
		/// Emits `AttributeCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(17)]
		#[pallet::weight(T::WeightInfo::clear_attribute())]
		pub fn clear_attribute(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: BoundedVec<u8, T::KeyLimit>,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}
			let maybe_is_frozen = match maybe_item {
				None => CollectionMetadataOf::<T, I>::get(collection).map(|v| v.is_frozen),
				Some(item) => ItemMetadataOf::<T, I>::get(collection, item).map(|v| v.is_frozen),
			};
			ensure!(!maybe_is_frozen.unwrap_or(false), Error::<T, I>::Frozen);

			if let Some((_, deposit)) = Attribute::<T, I>::take((collection, maybe_item, &key)) {
				collection_details.attributes.saturating_dec();
				collection_details.total_deposit.saturating_reduce(deposit);
				T::Currency::unreserve(&collection_details.owner, deposit);
				Collection::<T, I>::insert(collection, &collection_details);
				Self::deposit_event(Event::AttributeCleared { collection, maybe_item, key });
			}
			Ok(())
		}

		/// Set the metadata for an item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `collection`.
		///
		/// If the origin is Signed, then funds of signer are reserved according to the formula:
		/// `MetadataDepositBase + DepositPerByte * data.len` taking into
		/// account any already reserved funds.
		///
		/// - `collection`: The identifier of the collection whose item's metadata to set.
		/// - `item`: The identifier of the item whose metadata to set.
		/// - `data`: The general information of this item. Limited in length by `StringLimit`.
		/// - `is_frozen`: Whether the metadata should be frozen against further changes.
		///
		/// Emits `MetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(18)]
		#[pallet::weight(T::WeightInfo::set_metadata())]
		pub fn set_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			data: BoundedVec<u8, T::StringLimit>,
			is_frozen: bool,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}

			ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				if metadata.is_none() {
					collection_details.item_metadatas.saturating_inc();
				}
				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				collection_details.total_deposit.saturating_reduce(old_deposit);
				let mut deposit = Zero::zero();
				if !collection_details.free_holding && maybe_check_owner.is_some() {
					deposit = T::DepositPerByte::get()
						.saturating_mul(((data.len()) as u32).into())
						.saturating_add(T::MetadataDepositBase::get());
				}
				if deposit > old_deposit {
					T::Currency::reserve(&collection_details.owner, deposit - old_deposit)?;
				} else if deposit < old_deposit {
					T::Currency::unreserve(&collection_details.owner, old_deposit - deposit);
				}
				collection_details.total_deposit.saturating_accrue(deposit);

				*metadata = Some(ItemMetadata { deposit, data: data.clone(), is_frozen });

				Collection::<T, I>::insert(&collection, &collection_details);
				Self::deposit_event(Event::MetadataSet { collection, item, data, is_frozen });
				Ok(())
			})
		}

		/// Clear the metadata for an item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `item`.
		///
		/// Any deposit is freed for the collection's owner.
		///
		/// - `collection`: The identifier of the collection whose item's metadata to clear.
		/// - `item`: The identifier of the item whose metadata to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(19)]
		#[pallet::weight(T::WeightInfo::clear_metadata())]
		pub fn clear_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}

			ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				if metadata.is_some() {
					collection_details.item_metadatas.saturating_dec();
				}
				let deposit = metadata.take().ok_or(Error::<T, I>::UnknownCollection)?.deposit;
				T::Currency::unreserve(&collection_details.owner, deposit);
				collection_details.total_deposit.saturating_reduce(deposit);

				Collection::<T, I>::insert(&collection, &collection_details);
				Self::deposit_event(Event::MetadataCleared { collection, item });
				Ok(())
			})
		}

		/// Set the metadata for a collection.
		///
		/// Origin must be either `ForceOrigin` or `Signed` and the sender should be the Owner of
		/// the `collection`.
		///
		/// If the origin is `Signed`, then funds of signer are reserved according to the formula:
		/// `MetadataDepositBase + DepositPerByte * data.len` taking into
		/// account any already reserved funds.
		///
		/// - `collection`: The identifier of the item whose metadata to update.
		/// - `data`: The general information of this item. Limited in length by `StringLimit`.
		/// - `is_frozen`: Whether the metadata should be frozen against further changes.
		///
		/// Emits `CollectionMetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(20)]
		#[pallet::weight(T::WeightInfo::set_collection_metadata())]
		pub fn set_collection_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			data: BoundedVec<u8, T::StringLimit>,
			is_frozen: bool,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				details.total_deposit.saturating_reduce(old_deposit);
				let mut deposit = Zero::zero();
				if maybe_check_owner.is_some() && !details.free_holding {
					deposit = T::DepositPerByte::get()
						.saturating_mul(((data.len()) as u32).into())
						.saturating_add(T::MetadataDepositBase::get());
				}
				if deposit > old_deposit {
					T::Currency::reserve(&details.owner, deposit - old_deposit)?;
				} else if deposit < old_deposit {
					T::Currency::unreserve(&details.owner, old_deposit - deposit);
				}
				details.total_deposit.saturating_accrue(deposit);

				Collection::<T, I>::insert(&collection, details);

				*metadata = Some(CollectionMetadata { deposit, data: data.clone(), is_frozen });

				Self::deposit_event(Event::CollectionMetadataSet { collection, data, is_frozen });
				Ok(())
			})
		}

		/// Clear the metadata for a collection.
		///
		/// Origin must be either `ForceOrigin` or `Signed` and the sender should be the Owner of
		/// the `collection`.
		///
		/// Any deposit is freed for the collection's owner.
		///
		/// - `collection`: The identifier of the collection whose metadata to clear.
		///
		/// Emits `CollectionMetadataCleared`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(21)]
		#[pallet::weight(T::WeightInfo::clear_collection_metadata())]
		pub fn clear_collection_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
				let was_frozen = metadata.as_ref().map_or(false, |m| m.is_frozen);
				ensure!(maybe_check_owner.is_none() || !was_frozen, Error::<T, I>::Frozen);

				let deposit = metadata.take().ok_or(Error::<T, I>::UnknownCollection)?.deposit;
				T::Currency::unreserve(&details.owner, deposit);
				Self::deposit_event(Event::CollectionMetadataCleared { collection });
				Ok(())
			})
		}

		/// Set (or reset) the acceptance of ownership for a particular account.
		///
		/// Origin must be `Signed` and if `maybe_collection` is `Some`, then the signer must have a
		/// provider reference.
		///
		/// - `maybe_collection`: The identifier of the collection whose ownership the signer is
		///   willing to accept, or if `None`, an indication that the signer is willing to accept no
		///   ownership transferal.
		///
		/// Emits `OwnershipAcceptanceChanged`.
		#[pallet::call_index(22)]
		#[pallet::weight(T::WeightInfo::set_accept_ownership())]
		pub fn set_accept_ownership(
			origin: OriginFor<T>,
			maybe_collection: Option<T::CollectionId>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let old = OwnershipAcceptance::<T, I>::get(&who);
			match (old.is_some(), maybe_collection.is_some()) {
				(false, true) => {
					frame_system::Pallet::<T>::inc_consumers(&who)?;
				},
				(true, false) => {
					frame_system::Pallet::<T>::dec_consumers(&who);
				},
				_ => {},
			}
			if let Some(collection) = maybe_collection.as_ref() {
				OwnershipAcceptance::<T, I>::insert(&who, collection);
			} else {
				OwnershipAcceptance::<T, I>::remove(&who);
			}
			Self::deposit_event(Event::OwnershipAcceptanceChanged { who, maybe_collection });
			Ok(())
		}

		/// Set the maximum amount of items a collection could have.
		///
		/// Origin must be either `ForceOrigin` or `Signed` and the sender should be the Owner of
		/// the `collection`.
		///
		/// Note: This function can only succeed once per collection.
		///
		/// - `collection`: The identifier of the collection to change.
		/// - `max_supply`: The maximum amount of items a collection could have.
		///
		/// Emits `CollectionMaxSupplySet` event when successful.
		#[pallet::call_index(23)]
		#[pallet::weight(T::WeightInfo::set_collection_max_supply())]
		pub fn set_collection_max_supply(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			max_supply: u32,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			ensure!(
				!CollectionMaxSupply::<T, I>::contains_key(&collection),
				Error::<T, I>::MaxSupplyAlreadySet
			);

			let details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			ensure!(details.items <= max_supply, Error::<T, I>::MaxSupplyTooSmall);

			CollectionMaxSupply::<T, I>::insert(&collection, max_supply);
			Self::deposit_event(Event::CollectionMaxSupplySet { collection, max_supply });
			Ok(())
		}

		/// Set (or reset) the price for an item.
		///
		/// Origin must be Signed and must be the owner of the asset `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item to set the price for.
		/// - `price`: The price for the item. Pass `None`, to reset the price.
		/// - `buyer`: Restricts the buy operation to a specific account.
		///
		/// Emits `ItemPriceSet` on success if the price is not `None`.
		/// Emits `ItemPriceRemoved` on success if the price is `None`.
		#[pallet::call_index(24)]
		#[pallet::weight(T::WeightInfo::set_price())]
		pub fn set_price(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			price: Option<ItemPrice<T, I>>,
			whitelisted_buyer: Option<AccountIdLookupOf<T>>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let whitelisted_buyer = whitelisted_buyer.map(T::Lookup::lookup).transpose()?;
			Self::do_set_price(collection, item, origin, price, whitelisted_buyer)
		}

		/// Allows to buy an item if it's up for sale.
		///
		/// Origin must be Signed and must not be the owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item the sender wants to buy.
		/// - `bid_price`: The price the sender is willing to pay.
		///
		/// Emits `ItemBought` on success.
		#[pallet::call_index(25)]
		#[pallet::weight(T::WeightInfo::buy_item())]
		#[transactional]
		pub fn buy_item(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			bid_price: ItemPrice<T, I>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_buy_item(collection, item, origin, bid_price)
		}
	}
}
