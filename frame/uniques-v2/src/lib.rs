// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

mod general_features;
mod types;
mod user_features;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod mock;

pub use pallet::*;
use sp_runtime::traits::{IdentifyAccount, StaticLookup};
pub use types::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::{
		storage::bounded_btree_map::BoundedBTreeMap,
		traits::{
			fungibles::{Inspect, Transfer},
			Currency, ExistenceRequirement, ReservableCurrency,
		},
	};
	use sp_runtime::{
		traits::{CheckedAdd, One},
		AccountId32, MultiSignature, Perbill,
	};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId, Balance = Self::CurrencyBalance>;

		type CurrencyBalance: sp_runtime::traits::AtLeast32BitUnsigned
			+ codec::FullCodec
			+ Copy
			+ MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ Default
			+ From<u64>
			+ TypeInfo
			+ MaxEncodedLen;

		type AssetId: Member
			+ Parameter
			+ Default
			+ Copy
			+ codec::HasCompact
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen
			+ TypeInfo;

		type Assets: Inspect<Self::AccountId, AssetId = Self::AssetId, Balance = Self::CurrencyBalance>
			+ Transfer<Self::AccountId>;

		type CollectionId: Member + Parameter + Default + Copy + MaxEncodedLen + CheckedAdd + One;

		type ItemId: Member
			+ Parameter
			+ Default
			+ Copy
			+ MaxEncodedLen
			+ CheckedAdd
			+ One
			+ PartialOrd;

		/// This is the limit for metadata
		type MetadataLimit: Get<u32>; // = up to 10 kb;

		type DefaultSystemConfig: Get<SystemFeatures>;

		/// The maximum length of an attribute key.
		#[pallet::constant]
		type AttributeKeyLimit: Get<u32>;

		/// The maximum length of an attribute value.
		#[pallet::constant]
		type AttributeValueLimit: Get<u32>;

		/// The maximum amount of approvals an item could have.
		#[pallet::constant]
		type ApprovalsLimit: Get<u32>;
	}

	pub type MetadataOf<T> = BoundedVec<u8, <T as Config>::MetadataLimit>;
	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	pub type ApprovalsOf<T> = BoundedBTreeMap<
		<T as frame_system::Config>::AccountId,
		Option<<T as frame_system::Config>::BlockNumber>,
		<T as Config>::ApprovalsLimit,
	>;
	pub type AttributeKeyOf<T> = BoundedVec<u8, <T as Config>::AttributeKeyLimit>;
	pub type AttributeValueOf<T> = BoundedVec<u8, <T as Config>::AttributeValueLimit>;

	pub type BuyOfferOf<T> = BuyOffer<
		<T as Config>::CollectionId,
		<T as Config>::ItemId,
		BalanceOrAssetOf<T>,
		<T as frame_system::Config>::BlockNumber,
		<T as frame_system::Config>::AccountId,
	>;

	pub type SwapOfferOf<T> = SwapOffer<
		<T as Config>::CollectionId,
		<T as Config>::ItemId,
		BalanceOrAssetOf<T>,
		<T as frame_system::Config>::BlockNumber,
		<T as frame_system::Config>::AccountId,
	>;

	pub type AssetIdOf<T> =
		<<T as Config>::Assets as Inspect<<T as frame_system::Config>::AccountId>>::AssetId;
	pub type AssetBalanceOf<T> =
		<<T as Config>::Assets as Inspect<<T as frame_system::Config>::AccountId>>::Balance;
	pub type BalanceOrAssetOf<T> = BalanceOrAsset<BalanceOf<T>, AssetIdOf<T>, AssetBalanceOf<T>>;

	/// Maps a unique collection id to it's config.
	#[pallet::storage]
	pub(super) type CollectionConfigs<T: Config> =
		StorageMap<_, Blake2_128Concat, T::CollectionId, CollectionConfig>;

	/// Maps a unique collection id to it's administrator.
	#[pallet::storage]
	pub(super) type Admins<T: Config> =
		StorageMap<_, Blake2_128Concat, T::CollectionId, T::AccountId, OptionQuery>;

	/// Maps a collection id to it's metadata.
	#[pallet::storage]
	pub(super) type Collections<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Collection<T::CollectionId, T::AccountId, BalanceOf<T>>,
		OptionQuery,
	>;

	/// The collections owned by any given account; set out this way so that collections owned by
	/// a single account can be enumerated.
	#[pallet::storage]
	pub(super) type CollectionOwner<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		T::CollectionId,
		(),
		OptionQuery,
	>;

	/// The collections created by any given account; set out this way so that collections
	/// created by a single account can be enumerated.
	#[pallet::storage]
	pub(super) type CollectionCreator<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		T::CollectionId,
		(),
		OptionQuery,
	>;

	/// Stores the collection's next id.
	#[pallet::storage]
	pub(super) type CollectionNextId<T: Config> = StorageValue<_, T::CollectionId, ValueQuery>;

	#[pallet::storage]
	/// Metadata of an collection.
	pub(super) type CollectionMetadataOf<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionMetadata<MetadataOf<T>>,
		OptionQuery,
	>;

	/// Maps a collection id to it's items.
	#[pallet::storage]
	pub(super) type Items<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		Item<T::ItemId, T::AccountId, BalanceOf<T>, BalanceOrAssetOf<T>, ApprovalsOf<T>>,
		OptionQuery,
	>;

	/// The items held by any given account; set out this way so that items owned by a single
	/// account can be enumerated.
	#[pallet::storage]
	pub(super) type AccountItems<T: Config> = StorageNMap<
		_,
		(
			NMapKey<Blake2_128Concat, T::AccountId>, // owner
			NMapKey<Blake2_128Concat, T::CollectionId>,
			NMapKey<Blake2_128Concat, T::ItemId>,
		),
		(),
		OptionQuery,
	>;

	/// Keeps track of the number of items per collection per user.
	#[pallet::storage]
	pub(super) type CountForAccountItems<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		T::CollectionId,
		u32,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Metadata of an asset instance.
	pub(super) type ItemMetadataOf<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemMetadata<MetadataOf<T>>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Collection and items attributes.
	pub(super) type Attributes<T: Config> = StorageNMap<
		_,
		(
			NMapKey<Blake2_128Concat, T::CollectionId>,
			NMapKey<Blake2_128Concat, Option<T::ItemId>>,
			NMapKey<Blake2_128Concat, AttributeKeyOf<T>>,
		),
		AttributeValueOf<T>,
		OptionQuery,
	>;

	// Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CollectionCreated {
			id: T::CollectionId,
			max_supply: Option<u32>,
			max_items_per_account: Option<u32>,
			creator: T::AccountId,
			owner: T::AccountId,
			creator_royalties: Perbill,
			owner_royalties: Perbill,
		},
		CollectionMetadataSet {
			id: T::CollectionId,
			data: MetadataOf<T>,
		},
		CollectionLocked {
			id: T::CollectionId,
		},
		CollectionDestroyed {
			id: T::CollectionId,
		},
		CollectionOwnerChanged {
			id: T::CollectionId,
			old_owner: T::AccountId,
			new_owner: T::AccountId,
		},
		CollectionMaxSupplyChanged {
			id: T::CollectionId,
			max_supply: Option<u32>,
		},
		CollectionMaxItemsPerAccountChanged {
			id: T::CollectionId,
			max_items_per_account: Option<u32>,
		},
		CollectionConfigChanged {
			id: T::CollectionId,
		},
		ApprovalAdded {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			owner: T::AccountId,
			delegate: T::AccountId,
		},
		ApprovalsCleared {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			owner: T::AccountId,
		},
		ApprovalRemoved {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			owner: T::AccountId,
			delegate: T::AccountId,
		},
		AttributeSet {
			id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
			value: AttributeValueOf<T>,
		},
		AttributeCleared {
			id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
		},
		ItemCreated {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
		},
		ItemBurned {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
		},
		ItemTransferred {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			sender: T::AccountId,
			receiver: T::AccountId,
		},
		ItemMetadataSet {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			data: MetadataOf<T>,
		},
		ItemPriceSet {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			price: Option<BalanceOrAssetOf<T>>,
			buyer: Option<T::AccountId>,
		},
		ItemBought {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			price: BalanceOrAssetOf<T>,
			seller: T::AccountId,
			buyer: T::AccountId,
		},
		BuyOfferAccepted {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			price: BalanceOrAssetOf<T>,
			seller: T::AccountId,
			buyer: T::AccountId,
			receiver: T::AccountId,
			deadline: Option<T::BlockNumber>,
		},
		ItemsSwapExecuted {
			collection_from_id: T::CollectionId,
			item_from_id: T::ItemId,
			collection_to_id: T::CollectionId,
			item_to_id: T::ItemId,
			executed_by: T::AccountId,
			new_item_from_owner: T::AccountId,
			new_item_to_owner: T::AccountId,
			price: Option<BalanceOrAssetOf<T>>,
			deadline: Option<T::BlockNumber>,
		},
		CreatorRoyaltiesChanged {
			id: T::CollectionId,
			royalties: Perbill,
			creator: T::AccountId,
		},
		OwnerRoyaltiesChanged {
			id: T::CollectionId,
			royalties: Perbill,
			owner: T::AccountId,
		},
		CreatorRoyaltiesPaid {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			amount: BalanceOrAssetOf<T>,
			payer: T::AccountId,
			receiver: T::AccountId,
		},
		OwnerRoyaltiesPaid {
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			amount: BalanceOrAssetOf<T>,
			payer: T::AccountId,
			receiver: T::AccountId,
		},
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// The collection is not configured to do this operation.
		NotConfigured,
		/// A collection with this ID is already taken.
		CollectionIdTaken,
		/// A collection with this ID does not exist.
		CollectionNotFound,
		/// The collection is locked.
		CollectionIsLocked,
		/// An item with this ID is already claimed.
		ItemIdTaken,
		/// An item with this ID does not exist.
		ItemNotFound,
		/// Collection reached the maximum amount of items.
		AllItemsMinted,
		/// Items within that collection are non-transferable.
		ItemsNotTransferable,
		/// Item can't be sold.
		ItemNotForSale,
		/// Item underpriced.
		ItemUnderpriced,
		/// Wrong currency provided.
		WrongCurrency,
		/// User reached the limit of allowed items per collection per account
		CollectionItemsPerAccountLimitReached,
		/// The calling user is not authorized to make this call.
		NotAuthorized,
		/// The calling user has an approval that already expired.
		AuthorizationExpired,
		/// The delegate turned out to be different to what was expected.
		WrongDelegate,
		/// The hint provided by the user was incorrect.
		BadHint,
		/// An overflow has occurred.
		Overflow,
		/// Invalid witness data given.
		BadWitness,
		/// Trying to transfer or buy an item from oneself.
		TransferToSelf,
		/// User reached the limit of possible approvals per item.
		MaxApprovalsReached,
		/// Invalid signature provided.
		InvalidSignature,
		/// Invalid signature provided.
		ErrorConvertingToAccountId,
		/// Invalid item id provided.
		InvalidItemId,
		/// New value is bigger to the previous one.
		RoyaltiesBiggerToPreviousValue,
		/// Total royalties (creator's + owner's) exceed 100%.
		TotalRoyaltiesExceedHundredPercent,
	}

	// Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn create(
			origin: OriginFor<T>,
			owner: <T::Lookup as StaticLookup>::Source,
			config: UserFeatures,
			max_supply: Option<u32>,
			max_items_per_account: Option<u32>,
			creator_royalties: Perbill,
			owner_royalties: Perbill,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;

			let total = creator_royalties.checked_add(&owner_royalties);
			ensure!(
				total.map_or(false, |v| v < Perbill::one()),
				Error::<T>::TotalRoyaltiesExceedHundredPercent
			);

			Self::do_create_collection(
				sender,
				owner,
				config,
				max_supply,
				max_items_per_account,
				creator_royalties,
				owner_royalties,
			)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn change_collection_config(
			origin: OriginFor<T>,
			id: T::CollectionId,
			new_config: UserFeatures,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let current_config =
				CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_change_collection_config(id, sender, current_config, new_config)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn update_max_supply(
			origin: OriginFor<T>,
			id: T::CollectionId,
			max_supply: Option<u32>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_update_max_supply(id, sender, config, max_supply)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn update_max_items_per_account(
			origin: OriginFor<T>,
			id: T::CollectionId,
			max_items_per_account: Option<u32>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_update_max_items_per_account(id, sender, config, max_items_per_account)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn change_creator_royalties(
			origin: OriginFor<T>,
			id: T::CollectionId,
			royalties: Perbill,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_change_creator_royalties(sender, id, royalties)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn change_owner_royalties(
			origin: OriginFor<T>,
			id: T::CollectionId,
			royalties: Perbill,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_change_owner_royalties(sender, id, config, royalties)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn destroy(
			origin: OriginFor<T>,
			id: T::CollectionId,
			witness: DestroyWitness,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_destroy_collection(id, sender, config, witness)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn transfer_collection_ownership(
			origin: OriginFor<T>,
			id: T::CollectionId,
			new_owner: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let new_owner = T::Lookup::lookup(new_owner)?;
			Self::do_transfer_collection_ownership(id, sender, new_owner)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn approve_transfer(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			delegate: <T::Lookup as StaticLookup>::Source,
			deadline: Option<T::BlockNumber>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			let config =
				CollectionConfigs::<T>::get(collection_id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_approve_transfer(sender, collection_id, item_id, delegate, deadline, config)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn remove_transfer_approval(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			delegate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			Self::do_remove_transfer_approval(sender, collection_id, item_id, delegate)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn clear_all_transfer_approvals(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_clear_all_transfer_approvals(sender, collection_id, item_id)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_attribute(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
			value: AttributeValueOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_attributes(sender, collection_id, maybe_item, key, value)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn clear_attribute(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_clear_attribute(sender, collection_id, maybe_item, key)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn mint(
			origin: OriginFor<T>,
			owner: <T::Lookup as StaticLookup>::Source,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let owner = T::Lookup::lookup(owner)?;
			Self::do_mint_item(sender, owner, collection_id, item_id)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn burn(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_burn_item(sender, collection_id, item_id)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_admin(
			origin: OriginFor<T>,
			id: T::CollectionId,
			new_admin: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_admin(id, config, Some(sender), new_admin)?;
			Ok(())
		}

		// TODO: #[pallet::weight( Self::config_to_weight(config_hint) )]
		#[pallet::weight(0)]
		pub fn transfer_item(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			receiver: <T::Lookup as StaticLookup>::Source,
			config_hint: CollectionConfig,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let receiver = T::Lookup::lookup(receiver)?;
			let config =
				CollectionConfigs::<T>::get(collection_id).ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(config == config_hint, Error::<T>::BadHint);
			Self::do_transfer_item(collection_id, item_id, config, sender, receiver)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_collection_metadata(
			origin: OriginFor<T>,
			id: T::CollectionId,
			data: MetadataOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_collection_metadata(id, config, sender, data)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_item_metadata(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			data: MetadataOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_item_metadata(collection_id, item_id, sender, data)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_price(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			price: Option<BalanceOrAssetOf<T>>,
			buyer: Option<T::AccountId>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config =
				CollectionConfigs::<T>::get(collection_id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_price(collection_id, item_id, config, sender, price, buyer)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn buy_item(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			item_id: T::ItemId,
			bid_price: BalanceOrAssetOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config =
				CollectionConfigs::<T>::get(collection_id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_buy_item(collection_id, item_id, config, sender, bid_price)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn accept_buy_offer(
			origin: OriginFor<T>,
			offer: BuyOfferOf<T>,
			offer_signature: MultiSignature,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(offer.verify(&offer_signature), Error::<T>::InvalidSignature);

			let config = CollectionConfigs::<T>::get(offer.collection_id)
				.ok_or(Error::<T>::CollectionNotFound)?;

			let signer = offer.signer.into_account();
			let buyer = T::AccountId::decode(&mut AccountId32::as_ref(&signer))
				.map_err(|_| Error::<T>::ErrorConvertingToAccountId)?;

			Self::do_accept_buy_offer(
				sender,
				offer.collection_id,
				offer.item_id,
				config,
				buyer,
				offer.receiver,
				offer.item_owner,
				offer.bid_price,
				offer.deadline,
			)?;

			Ok(())
		}

		#[pallet::weight(0)]
		pub fn swap_items(
			origin: OriginFor<T>,
			offer: SwapOfferOf<T>,
			offer_signature: MultiSignature,
			item_to: T::ItemId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(offer.verify(&offer_signature), Error::<T>::InvalidSignature);

			let SwapOffer {
				collection_from_id,
				collection_to_id,
				item_from_id,
				item_to_id,
				signer,
				item_from_receiver,
				item_to_owner,
				price,
				deadline,
			} = offer;

			let config_from = CollectionConfigs::<T>::get(collection_from_id)
				.ok_or(Error::<T>::CollectionNotFound)?;
			let config_to = CollectionConfigs::<T>::get(collection_to_id)
				.ok_or(Error::<T>::CollectionNotFound)?;

			let signer = signer.into_account();
			let signer_account = T::AccountId::decode(&mut AccountId32::as_ref(&signer))
				.map_err(|_| Error::<T>::ErrorConvertingToAccountId)?;

			let item_to_id = match item_to_id {
				Some(item_to_id) => item_to_id,
				_ => item_to,
			};
			ensure!(item_to_id == item_to, Error::<T>::InvalidItemId);

			Self::do_swap_items(
				sender,
				collection_from_id,
				item_from_id,
				collection_to_id,
				item_to_id,
				config_from,
				config_to,
				signer_account,
				item_from_receiver,
				item_to_owner,
				price,
				deadline,
			)?;

			Ok(())
		}
	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {
		pub fn transfer(
			source: &T::AccountId,
			dest: &T::AccountId,
			value: BalanceOrAssetOf<T>,
			existence_requirement: ExistenceRequirement,
		) -> DispatchResult {
			use BalanceOrAsset::*;

			match value {
				Balance { amount } => {
					return T::Currency::transfer(&source, &dest, amount, existence_requirement);
				},
				Asset { id, amount } => {
					let keep_alive = existence_requirement == ExistenceRequirement::KeepAlive;
					return T::Assets::transfer(id, &source, &dest, amount, keep_alive).map(|_| ());
				},
			}
		}
	}
}
