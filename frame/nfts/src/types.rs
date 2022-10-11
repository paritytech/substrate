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

//! Various basic types for use in the Nfts pallet.

use super::*;
use crate::features::macros::*;
use codec::EncodeLike;
use enumflags2::{bitflags, BitFlags};
use frame_support::{
	pallet_prelude::{BoundedVec, MaxEncodedLen},
	traits::Get,
};
use scale_info::{build::Fields, meta_type, Path, Type, TypeInfo, TypeParameter};

pub(super) type DepositBalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
pub(super) type CollectionDetailsFor<T, I> =
	CollectionDetails<<T as SystemConfig>::AccountId, DepositBalanceOf<T, I>>;
pub(super) type ItemDetailsFor<T, I> =
	ItemDetails<<T as SystemConfig>::AccountId, DepositBalanceOf<T, I>, ApprovalsOf<T, I>>;
pub(super) type BalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
pub(super) type ItemPrice<T, I = ()> = BalanceOf<T, I>;
pub(super) type ItemTipOf<T, I = ()> = ItemTip<
	<T as Config<I>>::CollectionId,
	<T as Config<I>>::ItemId,
	<T as SystemConfig>::AccountId,
	BalanceOf<T, I>,
>;
pub(super) type CollectionConfigFor<T, I = ()> = CollectionConfig<
	BalanceOf<T, I>,
	<T as SystemConfig>::BlockNumber,
	<T as Config<I>>::CollectionId,
>;

pub trait Incrementable {
	fn increment(&self) -> Self;
	fn initial_value() -> Self;
}
impl_incrementable!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct CollectionDetails<AccountId, DepositBalance> {
	/// Can change `owner`, `issuer`, `freezer` and `admin` accounts.
	pub(super) owner: AccountId,
	/// Can mint tokens.
	pub(super) issuer: AccountId,
	/// Can thaw tokens, force transfers and burn tokens from any account.
	pub(super) admin: AccountId,
	/// Can freeze tokens.
	pub(super) freezer: AccountId,
	/// The total balance deposited for the all storage associated with this collection.
	/// Used by `destroy`.
	pub(super) total_deposit: DepositBalance,
	/// The total number of outstanding items of this collection.
	pub(super) items: u32,
	/// The total number of outstanding item metadata of this collection.
	pub(super) item_metadatas: u32,
	/// The total number of attributes for this collection.
	pub(super) attributes: u32,
}

/// Witness data for the destroy transactions.
#[derive(Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct DestroyWitness {
	/// The total number of outstanding items of this collection.
	#[codec(compact)]
	pub items: u32,
	/// The total number of items in this collection that have outstanding item metadata.
	#[codec(compact)]
	pub item_metadatas: u32,
	#[codec(compact)]
	/// The total number of attributes for this collection.
	pub attributes: u32,
}

impl<AccountId, DepositBalance> CollectionDetails<AccountId, DepositBalance> {
	pub fn destroy_witness(&self) -> DestroyWitness {
		DestroyWitness {
			items: self.items,
			item_metadatas: self.item_metadatas,
			attributes: self.attributes,
		}
	}
}

/// Information concerning the ownership of a single unique item.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct ItemDetails<AccountId, DepositBalance, Approvals> {
	/// The owner of this item.
	pub(super) owner: AccountId,
	/// The approved transferrer of this item, if one is set.
	pub(super) approvals: Approvals,
	/// The amount held in the pallet's default account for this item. Free-hold items will have
	/// this as zero.
	pub(super) deposit: DepositBalance,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(StringLimit))]
#[codec(mel_bound(DepositBalance: MaxEncodedLen))]
pub struct CollectionMetadata<DepositBalance, StringLimit: Get<u32>> {
	/// The balance deposited for this metadata.
	///
	/// This pays for the data stored in this struct.
	pub(super) deposit: DepositBalance,
	/// General information concerning this collection. Limited in length by `StringLimit`. This
	/// will generally be either a JSON dump or the hash of some JSON which can be found on a
	/// hash-addressable global publication system such as IPFS.
	pub(super) data: BoundedVec<u8, StringLimit>,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(StringLimit))]
#[codec(mel_bound(DepositBalance: MaxEncodedLen))]
pub struct ItemMetadata<DepositBalance, StringLimit: Get<u32>> {
	/// The balance deposited for this metadata.
	///
	/// This pays for the data stored in this struct.
	pub(super) deposit: DepositBalance,
	/// General information concerning this item. Limited in length by `StringLimit`. This will
	/// generally be either a JSON dump or the hash of some JSON which can be found on a
	/// hash-addressable global publication system such as IPFS.
	pub(super) data: BoundedVec<u8, StringLimit>,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct ItemTip<CollectionId, ItemId, AccountId, Amount> {
	/// A collection of the item.
	pub(super) collection: CollectionId,
	/// An item of which the tip is send for.
	pub(super) item: ItemId,
	/// A sender of the tip.
	pub(super) receiver: AccountId,
	/// An amount the sender is willing to tip.
	pub(super) amount: Amount,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct PendingSwap<CollectionId, ItemId, ItemPriceWithDirection, Deadline> {
	/// A collection of the item user wants to receive.
	pub(super) desired_collection: CollectionId,
	/// An item user wants to receive.
	pub(super) desired_item: Option<ItemId>,
	/// A price for the desired `item` with the direction.
	pub(super) price: Option<ItemPriceWithDirection>,
	/// An optional deadline for the swap.
	pub(super) deadline: Deadline,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum PriceDirection {
	Send,
	Receive,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct PriceWithDirection<Amount> {
	/// An amount.
	pub(super) amount: Amount,
	/// A direction (send or receive).
	pub(super) direction: PriceDirection,
}

// Support for up to 64 user-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum CollectionSetting {
	/// Disallow to transfer items in this collection.
	NonTransferableItems,
	/// Disallow to modify metadata of this collection.
	LockedMetadata,
	/// Disallow to modify attributes of this collection.
	LockedAttributes,
	/// Disallow to modify the supply of this collection.
	LockedMaxSupply,
	/// When is set then no deposit needed to hold items of this collection.
	FreeHolding,
}

/// Wrapper type for `BitFlags<CollectionSetting>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Eq, Default, RuntimeDebug)]
pub struct CollectionSettings(pub BitFlags<CollectionSetting>);

impl CollectionSettings {
	pub fn empty() -> Self {
		Self(BitFlags::EMPTY)
	}
	pub fn values(&self) -> BitFlags<CollectionSetting> {
		self.0
	}
}
impl_codec_bitflags!(CollectionSettings, u64, CollectionSetting);

#[derive(
	Clone, Copy, Encode, Decode, Default, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub enum MintType<CollectionId> {
	#[default]
	Private,
	Public,
	HolderOf(CollectionId),
}

#[derive(
	Clone, Copy, Encode, Decode, Default, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub struct MintSettings<Price, BlockNumber, CollectionId> {
	/// Mint type.
	pub(super) mint_type: MintType<CollectionId>,
	/// An optional price per mint.
	pub(super) price: Option<Price>,
	/// When the mint starts.
	pub(super) start_block: Option<BlockNumber>,
	/// When the mint ends.
	pub(super) end_block: Option<BlockNumber>,
	/// Whether the mint is limited. If `true` then only one `item` per account is possible to
	/// `mint`.
	/// NOTE: In order this to work, put the `NonTransferable` setting into
	/// `default_item_settings`.
	pub(super) limited: bool,
	/// Default settings each item will get during the mint.
	pub(super) default_item_settings: ItemSettings,
}

#[derive(
	Clone, Copy, RuntimeDebug, Decode, Default, Encode, MaxEncodedLen, PartialEq, TypeInfo,
)]
pub struct CollectionConfig<Price, BlockNumber, CollectionId> {
	/// Collection's settings.
	pub(super) settings: CollectionSettings,
	/// Collection's max supply.
	pub(super) max_supply: Option<u32>,
	/// Default settings each item will get during the mint.
	pub(super) mint_settings: MintSettings<Price, BlockNumber, CollectionId>,
}

// Support for up to 64 user-enabled features on an item.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum ItemSetting {
	/// Disallow transferring this item.
	NonTransferable,
	/// Disallow to modify metadata of this item.
	LockedMetadata,
	/// Disallow to modify attributes of this item.
	LockedAttributes,
}

/// Wrapper type for `BitFlags<ItemSetting>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Eq, Default, RuntimeDebug)]
pub struct ItemSettings(pub BitFlags<ItemSetting>);

impl ItemSettings {
	pub fn empty() -> Self {
		Self(BitFlags::EMPTY)
	}
	pub fn values(&self) -> BitFlags<ItemSetting> {
		self.0
	}
}
impl_codec_bitflags!(ItemSettings, u64, ItemSetting);

#[derive(
	Encode, Decode, Default, PartialEq, RuntimeDebug, Clone, Copy, MaxEncodedLen, TypeInfo,
)]
pub struct ItemConfig {
	/// Item's settings.
	pub(super) settings: ItemSettings,
}

// Support for up to 64 system-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum PalletFeature {
	/// Disallow trading operations.
	NoTrading,
	/// Disallow setting attributes.
	NoAttributes,
	/// Disallow transfer approvals.
	NoApprovals,
	/// Disallow atomic items swap.
	NoSwaps,
}

/// Wrapper type for `BitFlags<PalletFeature>` that implements `Codec`.
#[derive(Default, RuntimeDebug)]
pub struct PalletFeatures(pub BitFlags<PalletFeature>);

impl PalletFeatures {
	pub fn empty() -> Self {
		Self(BitFlags::EMPTY)
	}
}
impl_codec_bitflags!(PalletFeatures, u64, PalletFeature);
