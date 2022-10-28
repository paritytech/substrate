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

mod features;
mod functions;
mod impl_nonfungibles;
mod types;

pub mod macros;
pub mod weights;

use codec::{Decode, Encode};
use frame_support::{
	traits::{
		tokens::Locker, BalanceStatus::Reserved, Currency, EnsureOriginWithArg, ReservableCurrency,
	},
	BoundedBTreeMap,
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

type AccountIdLookupOf<T> = <<T as SystemConfig>::Lookup as StaticLookup>::Source;

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
		type CollectionId: Member + Parameter + MaxEncodedLen + Copy + Incrementable;

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

		/// The maximum approvals an item could have.
		#[pallet::constant]
		type ApprovalsLimit: Get<u32>;

		/// The max number of tips a user could send.
		#[pallet::constant]
		type MaxTips: Get<u32>;

		/// The max duration in blocks for deadlines.
		#[pallet::constant]
		type MaxDeadlineDuration: Get<<Self as SystemConfig>::BlockNumber>;

		/// Disables some of pallet's features.
		#[pallet::constant]
		type Features: Get<PalletFeatures>;

		#[cfg(feature = "runtime-benchmarks")]
		/// A set of helper functions for benchmarking.
		type Helper: BenchmarkHelper<Self::CollectionId, Self::ItemId>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// Details of a collection.
	#[pallet::storage]
	pub(super) type Collection<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionDetails<T::AccountId, DepositBalanceOf<T, I>>,
	>;

	/// The collection, if any, of which an account is willing to take ownership.
	#[pallet::storage]
	pub(super) type OwnershipAcceptance<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, T::CollectionId>;

	/// The items held by any given account; set out this way so that items owned by a single
	/// account can be enumerated.
	#[pallet::storage]
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

	/// The collections owned by any given account; set out this way so that collections owned by
	/// a single account can be enumerated.
	#[pallet::storage]
	pub(super) type CollectionAccount<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		T::CollectionId,
		(),
		OptionQuery,
	>;

	/// The items in existence and their ownership details.
	#[pallet::storage]
	/// Stores collection roles as per account.
	pub(super) type CollectionRoleOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::AccountId,
		CollectionRoles,
		OptionQuery,
	>;

	/// The items in existence and their ownership details.
	#[pallet::storage]
	pub(super) type Item<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemDetails<T::AccountId, DepositBalanceOf<T, I>, ApprovalsOf<T, I>>,
		OptionQuery,
	>;

	/// Metadata of a collection.
	#[pallet::storage]
	pub(super) type CollectionMetadataOf<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionMetadata<DepositBalanceOf<T, I>, T::StringLimit>,
		OptionQuery,
	>;

	/// Metadata of an item.
	#[pallet::storage]
	pub(super) type ItemMetadataOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemMetadata<DepositBalanceOf<T, I>, T::StringLimit>,
		OptionQuery,
	>;

	/// Attributes of a collection.
	#[pallet::storage]
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

	/// A price of an item.
	#[pallet::storage]
	pub(super) type ItemPriceOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		(ItemPrice<T, I>, Option<T::AccountId>),
		OptionQuery,
	>;

	/// Keeps track of the number of items a collection might have.
	#[pallet::storage]
	pub(super) type CollectionMaxSupply<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::CollectionId, u32, OptionQuery>;

	/// Stores the `CollectionId` that is going to be used for the next collection.
	/// This gets incremented by 1 whenever a new collection is created.
	#[pallet::storage]
	pub(super) type NextCollectionId<T: Config<I>, I: 'static = ()> =
		StorageValue<_, T::CollectionId, OptionQuery>;

	/// Handles all the pending swaps.
	#[pallet::storage]
	pub(super) type PendingSwapOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		PendingSwap<
			T::CollectionId,
			T::ItemId,
			PriceWithDirection<ItemPrice<T, I>>,
			<T as SystemConfig>::BlockNumber,
		>,
		OptionQuery,
	>;

	/// Config of a collection.
	#[pallet::storage]
	pub(super) type CollectionConfigOf<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::CollectionId, CollectionConfig, OptionQuery>;

	/// Config of an item.
	#[pallet::storage]
	pub(super) type ItemConfigOf<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemConfig,
		OptionQuery,
	>;

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
		/// An `item` became non-transferable.
		ItemTransferLocked { collection: T::CollectionId, item: T::ItemId },
		/// An `item` became transferable.
		ItemTransferUnlocked { collection: T::CollectionId, item: T::ItemId },
		/// `item` metadata or attributes were locked.
		ItemPropertiesLocked {
			collection: T::CollectionId,
			item: T::ItemId,
			lock_metadata: bool,
			lock_attributes: bool,
		},
		/// Some `collection` was locked.
		CollectionLocked { collection: T::CollectionId },
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
			deadline: Option<<T as SystemConfig>::BlockNumber>,
		},
		/// An approval for a `delegate` account to transfer the `item` of an item
		/// `collection` was cancelled by its `owner`.
		ApprovalCancelled {
			collection: T::CollectionId,
			item: T::ItemId,
			owner: T::AccountId,
			delegate: T::AccountId,
		},
		/// All approvals of an item got cancelled.
		AllApprovalsCancelled { collection: T::CollectionId, item: T::ItemId, owner: T::AccountId },
		/// A `collection` has had its attributes changed by the `Force` origin.
		CollectionStatusChanged { collection: T::CollectionId },
		/// New metadata has been set for a `collection`.
		CollectionMetadataSet { collection: T::CollectionId, data: BoundedVec<u8, T::StringLimit> },
		/// Metadata has been cleared for a `collection`.
		CollectionMetadataCleared { collection: T::CollectionId },
		/// New metadata has been set for an item.
		MetadataSet {
			collection: T::CollectionId,
			item: T::ItemId,
			data: BoundedVec<u8, T::StringLimit>,
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
		/// Event gets emmited when the `NextCollectionId` gets incremented.
		NextCollectionIdIncremented { next_id: T::CollectionId },
		/// The config of a collection has change.
		CollectionConfigChanged { id: T::CollectionId },
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
		/// A tip was sent.
		TipSent {
			collection: T::CollectionId,
			item: T::ItemId,
			sender: T::AccountId,
			receiver: T::AccountId,
			amount: DepositBalanceOf<T, I>,
		},
		/// An `item` swap intent was created.
		SwapCreated {
			offered_collection: T::CollectionId,
			offered_item: T::ItemId,
			desired_collection: T::CollectionId,
			desired_item: Option<T::ItemId>,
			price: Option<PriceWithDirection<ItemPrice<T, I>>>,
			deadline: <T as SystemConfig>::BlockNumber,
		},
		/// The swap was cancelled.
		SwapCancelled {
			offered_collection: T::CollectionId,
			offered_item: T::ItemId,
			desired_collection: T::CollectionId,
			desired_item: Option<T::ItemId>,
			price: Option<PriceWithDirection<ItemPrice<T, I>>>,
			deadline: <T as SystemConfig>::BlockNumber,
		},
		/// The swap has been claimed.
		SwapClaimed {
			sent_collection: T::CollectionId,
			sent_item: T::ItemId,
			sent_item_owner: T::AccountId,
			received_collection: T::CollectionId,
			received_item: T::ItemId,
			received_item_owner: T::AccountId,
			price: Option<PriceWithDirection<ItemPrice<T, I>>>,
			deadline: <T as SystemConfig>::BlockNumber,
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
		/// The approval had a deadline that expired, so the approval isn't valid anymore.
		ApprovalExpired,
		/// The owner turned out to be different to what was expected.
		WrongOwner,
		/// The witness data given does not match the current state of the chain.
		BadWitness,
		/// Collection ID is already taken.
		CollectionIdInUse,
		/// Items within that collection are non-transferable.
		ItemsNonTransferable,
		/// The provided account is not a delegate.
		NotDelegate,
		/// The delegate turned out to be different to what was expected.
		WrongDelegate,
		/// No approval exists that would allow the transfer.
		Unapproved,
		/// The named owner has not signed ownership acceptance of the collection.
		Unaccepted,
		/// The item is locked (non-transferable).
		ItemLocked,
		/// Item's attributes are locked.
		LockedItemAttributes,
		/// Collection's attributes are locked.
		LockedCollectionAttributes,
		/// Item's metadata is locked.
		LockedItemMetadata,
		/// Collection's metadata is locked.
		LockedCollectionMetadata,
		/// All items have been minted.
		MaxSupplyReached,
		/// The max supply has already been set.
		MaxSupplyAlreadySet,
		/// The provided max supply is less to the amount of items a collection already has.
		MaxSupplyTooSmall,
		/// The given item ID is unknown.
		UnknownItem,
		/// Swap doesn't exist.
		UnknownSwap,
		/// Item is not for sale.
		NotForSale,
		/// The provided bid is too low.
		BidTooLow,
		/// The item has reached its approval limit.
		ReachedApprovalLimit,
		/// The deadline has already expired.
		DeadlineExpired,
		/// The duration provided should be less or equal to MaxDeadlineDuration.
		WrongDuration,
		/// The method is disabled by system settings.
		MethodDisabled,
		/// The provided is setting can't be set.
		WrongSetting,
		/// Item's config already exists and should be equal to the provided one.
		InconsistentItemConfig,
		/// Config for a collection or an item can't be found.
		NoConfig,
		/// Some roles were not cleared.
		RolesNotCleared,
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
		/// The origin must be Signed and the sender must have sufficient funds free.
		///
		/// `ItemDeposit` funds of sender are reserved.
		///
		/// Parameters:
		/// - `admin`: The admin of this collection. The admin is the initial address of each
		/// member of the collection's admin team.
		///
		/// Emits `Created` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::create())]
		pub fn create(
			origin: OriginFor<T>,
			admin: AccountIdLookupOf<T>,
			config: CollectionConfig,
		) -> DispatchResult {
			let collection =
				NextCollectionId::<T, I>::get().unwrap_or(T::CollectionId::initial_value());

			let owner = T::CreateOrigin::ensure_origin(origin, &collection)?;
			let admin = T::Lookup::lookup(admin)?;

			// DepositRequired can be disabled by calling the force_create() only
			ensure!(
				!config.has_disabled_setting(CollectionSetting::DepositRequired),
				Error::<T, I>::WrongSetting
			);

			Self::do_create_collection(
				collection,
				owner.clone(),
				admin.clone(),
				config,
				T::CollectionDeposit::get(),
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
		/// - `owner`: The owner of this collection of items. The owner has full superuser
		///   permissions
		/// over this item, but may later change and configure the permissions using
		/// `transfer_ownership` and `set_team`.
		///
		/// Emits `ForceCreated` event when successful.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_create())]
		pub fn force_create(
			origin: OriginFor<T>,
			owner: AccountIdLookupOf<T>,
			config: CollectionConfig,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			let collection =
				NextCollectionId::<T, I>::get().unwrap_or(T::CollectionId::initial_value());

			Self::do_create_collection(
				collection,
				owner.clone(),
				owner.clone(),
				config,
				Zero::zero(),
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
		#[pallet::weight(T::WeightInfo::mint())]
		pub fn mint(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			owner: AccountIdLookupOf<T>,
			config: ItemConfig,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			ensure!(
				Self::has_role(&collection, &origin, CollectionRole::Issuer),
				Error::<T, I>::NoPermission
			);
			Self::do_mint(collection, item, owner, config)
		}

		/// Destroy a single item.
		///
		/// Origin must be Signed and the sender should be the Admin of the `collection`.
		///
		/// - `collection`: The collection of the item to be burned.
		/// - `item`: The item to be burned.
		/// - `check_owner`: If `Some` then the operation will fail with `WrongOwner` unless the
		///   item is owned by this value.
		///
		/// Emits `Burned` with the actual amount burned.
		///
		/// Weight: `O(1)`
		/// Modes: `check_owner.is_some()`.
		#[pallet::weight(T::WeightInfo::burn())]
		pub fn burn(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			check_owner: Option<AccountIdLookupOf<T>>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let check_owner = check_owner.map(T::Lookup::lookup).transpose()?;

			Self::do_burn(collection, item, |details| {
				let is_admin = Self::has_role(&collection, &origin, CollectionRole::Admin);
				let is_permitted = is_admin || details.owner == origin;
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
		/// Origin must be Signed and the signing account must be either:
		/// - the Admin of the `collection`;
		/// - the Owner of the `item`;
		/// - the approved delegate for the `item` (in this case, the approval is reset).
		///
		/// Arguments:
		/// - `collection`: The collection of the item to be transferred.
		/// - `item`: The item to be transferred.
		/// - `dest`: The account to receive ownership of the item.
		///
		/// Emits `Transferred`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::transfer())]
		pub fn transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			dest: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			Self::do_transfer(collection, item, dest, |_, details| {
				let is_admin = Self::has_role(&collection, &origin, CollectionRole::Admin);
				if details.owner != origin && !is_admin {
					let deadline =
						details.approvals.get(&origin).ok_or(Error::<T, I>::NoPermission)?;
					if let Some(d) = deadline {
						let block_number = frame_system::Pallet::<T>::block_number();
						ensure!(block_number <= *d, Error::<T, I>::ApprovalExpired);
					}
				}
				Ok(())
			})
		}

		/// Re-evaluate the deposits on some items.
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

			let config = Self::get_collection_config(&collection)?;
			let deposit = match config.is_setting_enabled(CollectionSetting::DepositRequired) {
				true => T::ItemDeposit::get(),
				false => Zero::zero(),
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
		/// - `collection`: The collection of the item to be changed.
		/// - `item`: The item to become non-transferable.
		///
		/// Emits `ItemTransferLocked`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::lock_item_transfer())]
		pub fn lock_item_transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_lock_item_transfer(origin, collection, item)
		}

		/// Re-allow unprivileged transfer of an item.
		///
		/// Origin must be Signed and the sender should be the Freezer of the `collection`.
		///
		/// - `collection`: The collection of the item to be changed.
		/// - `item`: The item to become transferable.
		///
		/// Emits `ItemTransferUnlocked`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::unlock_item_transfer())]
		pub fn unlock_item_transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_unlock_item_transfer(origin, collection, item)
		}

		/// Disallows specified settings for the whole collection.
		///
		/// Origin must be Signed and the sender should be the Freezer of the `collection`.
		///
		/// - `collection`: The collection to be locked.
		/// - `lock_config`: The config with the settings to be locked.
		///
		/// Note: it's possible to only lock(set) the setting, but not to unset it.
		/// Emits `CollectionLocked`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::lock_collection())]
		pub fn lock_collection(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			lock_config: CollectionConfig,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_lock_collection(origin, collection, lock_config)
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

				// delete previous values
				Self::clear_roles(&collection)?;

				let account_to_role = Self::group_roles_by_account(vec![
					(issuer.clone(), CollectionRole::Issuer),
					(admin.clone(), CollectionRole::Admin),
					(freezer.clone(), CollectionRole::Freezer),
				]);
				for (account, roles) in account_to_role {
					CollectionRoleOf::<T, I>::insert(&collection, &account, roles);
				}

				Self::deposit_event(Event::TeamChanged { collection, issuer, admin, freezer });
				Ok(())
			})
		}

		/// Approve an item to be transferred by a delegated third-party account.
		///
		/// Origin must be Signed and must be the owner of the `item`.
		///
		/// - `collection`: The collection of the item to be approved for delegated transfer.
		/// - `item`: The item to be approved for delegated transfer.
		/// - `delegate`: The account to delegate permission to transfer the item.
		/// - `maybe_deadline`: Optional deadline for the approval. Specified by providing the
		/// 	number of blocks after which the approval will expire
		///
		/// Emits `ApprovedTransfer` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::approve_transfer())]
		pub fn approve_transfer(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			delegate: AccountIdLookupOf<T>,
			maybe_deadline: Option<<T as SystemConfig>::BlockNumber>,
		) -> DispatchResult {
			ensure!(
				Self::is_pallet_feature_enabled(PalletFeature::Approvals),
				Error::<T, I>::MethodDisabled
			);
			let maybe_check: Option<T::AccountId> = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			let delegate = T::Lookup::lookup(delegate)?;

			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;

			let collection_config = Self::get_collection_config(&collection)?;
			ensure!(
				collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
				Error::<T, I>::ItemsNonTransferable
			);

			let collection_config = Self::get_collection_config(&collection)?;
			ensure!(
				collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
				Error::<T, I>::ItemsNonTransferable
			);

			if let Some(check) = maybe_check {
				let is_admin = Self::has_role(&collection, &check, CollectionRole::Admin);
				let permitted = is_admin || check == details.owner;
				ensure!(permitted, Error::<T, I>::NoPermission);
			}

			let now = frame_system::Pallet::<T>::block_number();
			let deadline = maybe_deadline.map(|d| d.saturating_add(now));

			details
				.approvals
				.try_insert(delegate.clone(), deadline)
				.map_err(|_| Error::<T, I>::ReachedApprovalLimit)?;
			Item::<T, I>::insert(&collection, &item, &details);

			Self::deposit_event(Event::ApprovedTransfer {
				collection,
				item,
				owner: details.owner,
				delegate,
				deadline,
			});

			Ok(())
		}

		/// Cancel one of the transfer approvals for a specific item.
		///
		/// Origin must be either:
		/// - the `Force` origin;
		/// - `Signed` with the signer being the Admin of the `collection`;
		/// - `Signed` with the signer being the Owner of the `item`;
		///
		/// Arguments:
		/// - `collection`: The collection of the item of whose approval will be cancelled.
		/// - `item`: The item of the collection of whose approval will be cancelled.
		/// - `delegate`: The account that is going to loose their approval.
		///
		/// Emits `ApprovalCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::cancel_approval())]
		pub fn cancel_approval(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			delegate: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let maybe_check: Option<T::AccountId> = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			let delegate = T::Lookup::lookup(delegate)?;

			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;

			let maybe_deadline =
				details.approvals.get(&delegate).ok_or(Error::<T, I>::NotDelegate)?;

			let is_past_deadline = if let Some(deadline) = maybe_deadline {
				let now = frame_system::Pallet::<T>::block_number();
				now > *deadline
			} else {
				false
			};

			if !is_past_deadline {
				if let Some(check) = maybe_check {
					let is_admin = Self::has_role(&collection, &check, CollectionRole::Admin);
					let permitted = is_admin || check == details.owner;
					ensure!(permitted, Error::<T, I>::NoPermission);
				}
			}

			details.approvals.remove(&delegate);
			Item::<T, I>::insert(&collection, &item, &details);
			Self::deposit_event(Event::ApprovalCancelled {
				collection,
				item,
				owner: details.owner,
				delegate,
			});

			Ok(())
		}

		/// Cancel all the approvals of a specific item.
		///
		/// Origin must be either:
		/// - the `Force` origin;
		/// - `Signed` with the signer being the Admin of the `collection`;
		/// - `Signed` with the signer being the Owner of the `item`;
		///
		/// Arguments:
		/// - `collection`: The collection of the item of whose approvals will be cleared.
		/// - `item`: The item of the collection of whose approvals will be cleared.
		///
		/// Emits `AllApprovalsCancelled` on success.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::clear_all_transfer_approvals())]
		pub fn clear_all_transfer_approvals(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
		) -> DispatchResult {
			let maybe_check: Option<T::AccountId> = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			let mut details =
				Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;

			if let Some(check) = maybe_check {
				let is_admin = Self::has_role(&collection, &check, CollectionRole::Admin);
				let permitted = is_admin || check == details.owner;
				ensure!(permitted, Error::<T, I>::NoPermission);
			}

			details.approvals.clear();
			Item::<T, I>::insert(&collection, &item, &details);
			Self::deposit_event(Event::AllApprovalsCancelled {
				collection,
				item,
				owner: details.owner,
			});

			Ok(())
		}

		/// Alter the attributes of a given collection.
		///
		/// Origin must be `ForceOrigin`.
		///
		/// - `collection`: The identifier of the collection.
		/// - `owner`: The new Owner of this collection.
		/// - `issuer`: The new Issuer of this collection.
		/// - `admin`: The new Admin of this collection.
		/// - `freezer`: The new Freezer of this collection.
		/// - `config`: Collection's config.
		///
		/// Emits `CollectionStatusChanged` with the identity of the item.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::force_collection_status())]
		pub fn force_collection_status(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			owner: AccountIdLookupOf<T>,
			issuer: AccountIdLookupOf<T>,
			admin: AccountIdLookupOf<T>,
			freezer: AccountIdLookupOf<T>,
			config: CollectionConfig,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			Collection::<T, I>::try_mutate(collection, |maybe_collection| {
				let mut collection_info =
					maybe_collection.take().ok_or(Error::<T, I>::UnknownCollection)?;
				let old_owner = collection_info.owner;
				let new_owner = T::Lookup::lookup(owner)?;
				collection_info.owner = new_owner.clone();
				*maybe_collection = Some(collection_info);
				CollectionAccount::<T, I>::remove(&old_owner, &collection);
				CollectionAccount::<T, I>::insert(&new_owner, &collection, ());
				CollectionConfigOf::<T, I>::insert(&collection, config);

				let issuer = T::Lookup::lookup(issuer)?;
				let admin = T::Lookup::lookup(admin)?;
				let freezer = T::Lookup::lookup(freezer)?;

				// delete previous values
				Self::clear_roles(&collection)?;

				let account_to_role = Self::group_roles_by_account(vec![
					(issuer, CollectionRole::Issuer),
					(admin, CollectionRole::Admin),
					(freezer, CollectionRole::Freezer),
				]);
				for (account, roles) in account_to_role {
					CollectionRoleOf::<T, I>::insert(&collection, &account, roles);
				}

				Self::deposit_event(Event::CollectionStatusChanged { collection });
				Ok(())
			})
		}

		/// Disallows changing the metadata of attributes of the item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `collection`.
		///
		/// - `collection`: The collection if the `item`.
		/// - `item`: An item to be locked.
		/// - `lock_config`: The config with the settings to be locked.
		///
		/// Note: when the metadata or attributes are locked, it won't be possible the unlock them.
		/// Emits `ItemPropertiesLocked`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::lock_item_properties())]
		pub fn lock_item_properties(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			lock_metadata: bool,
			lock_attributes: bool,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			Self::do_lock_item_properties(
				maybe_check_owner,
				collection,
				item,
				lock_metadata,
				lock_attributes,
			)
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
		#[pallet::weight(T::WeightInfo::set_attribute())]
		pub fn set_attribute(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: BoundedVec<u8, T::KeyLimit>,
			value: BoundedVec<u8, T::ValueLimit>,
		) -> DispatchResult {
			ensure!(
				Self::is_pallet_feature_enabled(PalletFeature::Attributes),
				Error::<T, I>::MethodDisabled
			);
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}

			let collection_config = Self::get_collection_config(&collection)?;
			match maybe_item {
				None => {
					ensure!(
						collection_config.is_setting_enabled(CollectionSetting::UnlockedAttributes),
						Error::<T, I>::LockedCollectionAttributes
					)
				},
				Some(item) => {
					let maybe_is_locked = Self::get_item_config(&collection, &item)
						.map(|c| c.has_disabled_setting(ItemSetting::UnlockedAttributes))?;
					ensure!(!maybe_is_locked, Error::<T, I>::LockedItemAttributes);
				},
			};

			let attribute = Attribute::<T, I>::get((collection, maybe_item, &key));
			if attribute.is_none() {
				collection_details.attributes.saturating_inc();
			}
			let old_deposit = attribute.map_or(Zero::zero(), |m| m.1);
			collection_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if collection_config.is_setting_enabled(CollectionSetting::DepositRequired) &&
				maybe_check_owner.is_some()
			{
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

			if maybe_check_owner.is_some() {
				match maybe_item {
					None => {
						let collection_config = Self::get_collection_config(&collection)?;
						ensure!(
							collection_config
								.is_setting_enabled(CollectionSetting::UnlockedAttributes),
							Error::<T, I>::LockedCollectionAttributes
						)
					},
					Some(item) => {
						// NOTE: if the item was previously burned, the ItemSettings record might
						// not exists. In that case, we allow to clear the attribute.
						let maybe_is_locked = Self::get_item_config(&collection, &item)
							.map_or(false, |c| {
								c.has_disabled_setting(ItemSetting::UnlockedAttributes)
							});
						ensure!(!maybe_is_locked, Error::<T, I>::LockedItemAttributes);
					},
				};
			}

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
		///
		/// Emits `MetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_metadata())]
		pub fn set_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			data: BoundedVec<u8, T::StringLimit>,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

			let item_config = Self::get_item_config(&collection, &item)?;
			ensure!(
				maybe_check_owner.is_none() ||
					item_config.is_setting_enabled(ItemSetting::UnlockedMetadata),
				Error::<T, I>::LockedItemMetadata
			);

			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
			}

			let collection_config = Self::get_collection_config(&collection)?;

			ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
				if metadata.is_none() {
					collection_details.item_metadatas.saturating_inc();
				}
				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				collection_details.total_deposit.saturating_reduce(old_deposit);
				let mut deposit = Zero::zero();
				if collection_config.is_setting_enabled(CollectionSetting::DepositRequired) &&
					maybe_check_owner.is_some()
				{
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

				*metadata = Some(ItemMetadata { deposit, data: data.clone() });

				Collection::<T, I>::insert(&collection, &collection_details);
				Self::deposit_event(Event::MetadataSet { collection, item, data });
				Ok(())
			})
		}

		/// Clear the metadata for an item.
		///
		/// Origin must be either `ForceOrigin` or Signed and the sender should be the Owner of the
		/// `collection`.
		///
		/// Any deposit is freed for the collection's owner.
		///
		/// - `collection`: The identifier of the collection whose item's metadata to clear.
		/// - `item`: The identifier of the item whose metadata to clear.
		///
		/// Emits `MetadataCleared`.
		///
		/// Weight: `O(1)`
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

			// NOTE: if the item was previously burned, the ItemSettings record might not exists
			let is_locked = Self::get_item_config(&collection, &item)
				.map_or(false, |c| c.has_disabled_setting(ItemSetting::UnlockedMetadata));

			ensure!(maybe_check_owner.is_none() || !is_locked, Error::<T, I>::LockedItemMetadata);

			ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
				if metadata.is_some() {
					collection_details.item_metadatas.saturating_dec();
				}
				let deposit = metadata.take().ok_or(Error::<T, I>::UnknownItem)?.deposit;
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
		///
		/// Emits `CollectionMetadataSet`.
		///
		/// Weight: `O(1)`
		#[pallet::weight(T::WeightInfo::set_collection_metadata())]
		pub fn set_collection_metadata(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			data: BoundedVec<u8, T::StringLimit>,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some))?;

			let collection_config = Self::get_collection_config(&collection)?;
			ensure!(
				maybe_check_owner.is_none() ||
					collection_config.is_setting_enabled(CollectionSetting::UnlockedMetadata),
				Error::<T, I>::LockedCollectionMetadata
			);

			let mut details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = &maybe_check_owner {
				ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
			}

			CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
				let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
				details.total_deposit.saturating_reduce(old_deposit);
				let mut deposit = Zero::zero();
				if maybe_check_owner.is_some() &&
					collection_config.is_setting_enabled(CollectionSetting::DepositRequired)
				{
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

				*metadata = Some(CollectionMetadata { deposit, data: data.clone() });

				Self::deposit_event(Event::CollectionMetadataSet { collection, data });
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

			let collection_config = Self::get_collection_config(&collection)?;
			ensure!(
				maybe_check_owner.is_none() ||
					collection_config.is_setting_enabled(CollectionSetting::UnlockedMetadata),
				Error::<T, I>::LockedCollectionMetadata
			);

			CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
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
		#[pallet::weight(T::WeightInfo::buy_item())]
		pub fn buy_item(
			origin: OriginFor<T>,
			collection: T::CollectionId,
			item: T::ItemId,
			bid_price: ItemPrice<T, I>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_buy_item(collection, item, origin, bid_price)
		}

		/// Allows to pay the tips.
		///
		/// Origin must be Signed.
		///
		/// - `tips`: Tips array.
		///
		/// Emits `TipSent` on every tip transfer.
		#[pallet::weight(T::WeightInfo::pay_tips(tips.len() as u32))]
		pub fn pay_tips(
			origin: OriginFor<T>,
			tips: BoundedVec<ItemTipOf<T, I>, T::MaxTips>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_pay_tips(origin, tips)
		}

		/// Register a new atomic swap, declaring an intention to send an `item` in exchange for
		/// `desired_item` from origin to target on the current blockchain.
		/// The target can execute the swap during the specified `duration` of blocks (if set).
		/// Additionally, the price could be set for the desired `item`.
		///
		/// Origin must be Signed and must be an owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item an owner wants to give.
		/// - `desired_collection`: The collection of the desired item.
		/// - `desired_item`: The desired item an owner wants to receive.
		/// - `maybe_price`: The price an owner is willing to pay or receive for the desired `item`.
		/// - `maybe_duration`: Optional deadline for the swap. Specified by providing the
		/// 	number of blocks after which the swap will expire.
		///
		/// Emits `SwapCreated` on success.
		#[pallet::weight(T::WeightInfo::create_swap())]
		pub fn create_swap(
			origin: OriginFor<T>,
			offered_collection: T::CollectionId,
			offered_item: T::ItemId,
			desired_collection: T::CollectionId,
			maybe_desired_item: Option<T::ItemId>,
			maybe_price: Option<PriceWithDirection<ItemPrice<T, I>>>,
			duration: <T as SystemConfig>::BlockNumber,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_create_swap(
				origin,
				offered_collection,
				offered_item,
				desired_collection,
				maybe_desired_item,
				maybe_price,
				duration,
			)
		}

		/// Cancel an atomic swap.
		///
		/// Origin must be Signed.
		/// Origin must be an owner of the `item` if the deadline hasn't expired.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item an owner wants to give.
		///
		/// Emits `SwapCancelled` on success.
		#[pallet::weight(T::WeightInfo::cancel_swap())]
		pub fn cancel_swap(
			origin: OriginFor<T>,
			offered_collection: T::CollectionId,
			offered_item: T::ItemId,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_cancel_swap(origin, offered_collection, offered_item)
		}

		/// Claim an atomic swap.
		/// This method executes a pending swap, that was created by a counterpart before.
		///
		/// Origin must be Signed and must be an owner of the `item`.
		///
		/// - `send_collection`: The collection of the item to be sent.
		/// - `send_item`: The item to be sent.
		/// - `receive_collection`: The collection of the item to be received.
		/// - `receive_item`: The item to be received.
		/// - `witness_price`: A price that was previously agreed on.
		///
		/// Emits `SwapClaimed` on success.
		#[pallet::weight(T::WeightInfo::claim_swap())]
		pub fn claim_swap(
			origin: OriginFor<T>,
			send_collection: T::CollectionId,
			send_item: T::ItemId,
			receive_collection: T::CollectionId,
			receive_item: T::ItemId,
			witness_price: Option<PriceWithDirection<ItemPrice<T, I>>>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::do_claim_swap(
				origin,
				send_collection,
				send_item,
				receive_collection,
				receive_item,
				witness_price,
			)
		}
	}
}
