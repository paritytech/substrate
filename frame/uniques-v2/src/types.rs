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

use codec::{Decode, Encode, MaxEncodedLen};
use enumflags2::{bitflags, BitFlags};
use frame_support::RuntimeDebug;
use scale_info::{build::Fields, meta_type, Path, Type, TypeInfo, TypeParameter};
use sp_runtime::{
	traits::{IdentifyAccount, Verify},
	MultiSignature, MultiSigner, Perbill,
};

// Support for up to 64 user-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum UserFeature {
	Administration,
	IsLocked,
	NonTransferableItems,
}

/// Wrapper type for `BitFlags<UserFeature>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Eq, Default, RuntimeDebug)]
pub struct UserFeatures(pub BitFlags<UserFeature>);

impl UserFeatures {
	pub fn new(input: BitFlags<UserFeature>) -> Self {
		UserFeatures(input)
	}

	pub fn get(&self) -> BitFlags<UserFeature> {
		self.0.clone()
	}
}

impl MaxEncodedLen for UserFeatures {
	fn max_encoded_len() -> usize {
		u64::max_encoded_len()
	}
}

impl Encode for UserFeatures {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.bits().using_encoded(f)
	}
}
impl Decode for UserFeatures {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let field = u64::decode(input)?;
		Ok(Self(<BitFlags<UserFeature>>::from_bits(field as u64).map_err(|_| "invalid value")?))
	}
}
impl TypeInfo for UserFeatures {
	type Identity = Self;

	fn type_info() -> Type {
		Type::builder()
			.path(Path::new("BitFlags", module_path!()))
			.type_params(vec![TypeParameter::new("T", Some(meta_type::<UserFeature>()))])
			.composite(Fields::unnamed().field(|f| f.ty::<u64>().type_name("UserFeature")))
	}
}

// Support for up to 64 system-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum SystemFeature {
	NoDeposit,
	CreatorRoyalties,
	OwnerRoyalties,
}

/// Wrapper type for `BitFlags<UserFeature>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Default, RuntimeDebug)]
pub struct SystemFeatures(pub BitFlags<SystemFeature>);

impl SystemFeatures {
	pub fn new(input: BitFlags<SystemFeature>) -> Self {
		SystemFeatures(input)
	}

	pub fn get(&self) -> BitFlags<SystemFeature> {
		self.0.clone()
	}
}

impl MaxEncodedLen for SystemFeatures {
	fn max_encoded_len() -> usize {
		u64::max_encoded_len()
	}
}

impl Eq for SystemFeatures {}
impl Encode for SystemFeatures {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.bits().using_encoded(f)
	}
}
impl Decode for SystemFeatures {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let field = u64::decode(input)?;
		Ok(Self(<BitFlags<SystemFeature>>::from_bits(field as u64).map_err(|_| "invalid value")?))
	}
}
impl TypeInfo for SystemFeatures {
	type Identity = Self;

	fn type_info() -> Type {
		Type::builder()
			.path(Path::new("BitFlags", module_path!()))
			.type_params(vec![TypeParameter::new("T", Some(meta_type::<SystemFeature>()))])
			.composite(Fields::unnamed().field(|f| f.ty::<u64>().type_name("SystemFeature")))
	}
}

// TODO: Implement Default

#[derive(Encode, Decode, PartialEq, Debug, Clone, Copy, MaxEncodedLen, TypeInfo)]
pub struct CollectionConfig {
	pub system_features: SystemFeatures,
	pub user_features: UserFeatures,
}

#[derive(Encode, Decode, PartialEq, Default, MaxEncodedLen, TypeInfo)]
pub struct Collection<CollectionId, Account, Balance> {
	pub id: CollectionId,
	pub creator: Account,
	pub owner: Account,
	pub deposit: Option<Balance>,
	pub attributes: u32,
	pub items: u32,
	pub item_metadatas: u32,
	pub max_supply: Option<u32>,
	pub max_items_per_account: Option<u32>,
	pub creator_royalties: Perbill,
	pub owner_royalties: Perbill,
}

#[derive(Encode, Decode, PartialEq, Default, MaxEncodedLen, TypeInfo)]
pub struct Item<ItemId, Account, Balance, BalanceOrAsset, Approvals> {
	pub id: ItemId,
	pub owner: Account,
	pub deposit: Option<Balance>,
	// `None` assumes not for sale
	pub price: Option<BalanceOrAsset>,
	// `None` assumes anyone can buy
	pub buyer: Option<Account>,
	pub approvals: Approvals,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
#[codec(mel_bound(Metadata: MaxEncodedLen))]
pub struct CollectionMetadata<Metadata> {
	/// General information concerning this asset. Limited in length by `StringLimit`. This will
	/// generally be either a JSON dump or the hash of some JSON which can be found on a
	/// hash-addressable global publication system such as IPFS.
	pub(super) data: Metadata,
}

#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
#[codec(mel_bound(Metadata: MaxEncodedLen))]
pub struct ItemMetadata<Metadata> {
	/// General information concerning this asset. Limited in length by `StringLimit`. This will
	/// generally be either a JSON dump or the hash of some JSON which can be found on a
	/// hash-addressable global publication system such as IPFS.
	pub(super) data: Metadata,
}

/// Witness data for the destroy transactions.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, Default, TypeInfo, MaxEncodedLen)]
pub struct DestroyWitness {
	/// The total number of outstanding instances of this asset class.
	#[codec(compact)]
	pub items: u32,
	/// The total number of outstanding instance metadata of this asset class.
	#[codec(compact)]
	pub item_metadatas: u32,
	/// The total number of attributes for this asset class.
	#[codec(compact)]
	pub attributes: u32,
}

/// Authorization to buy an item.
///
/// This is signed by an off-chain participant to authorize
/// an on-chain item buy operation by a specific on-chain account.
///
/// NOTE: The signature is not part of the struct.
#[derive(Encode, Decode, Clone, PartialEq, RuntimeDebug, TypeInfo)]
#[codec(dumb_trait_bound)]
pub struct BuyOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId> {
	/// Collection id.
	pub collection_id: CollectionId,
	/// An item id to buy.
	pub item_id: ItemId,
	/// A price the buyer offers.
	pub bid_price: Balance,
	/// A block number this is offer is valid until
	pub deadline: Option<BlockNumber>,
	/// Item's owner, will be credited with `bid_price`.
	pub item_owner: AccountId,
	/// Off-chain buyer to debit.
	pub signer: MultiSigner,
	/// An account that will receive an item.
	pub receiver: AccountId,
}

/// Authorization to swap an item.
///
/// This is signed by an off-chain participant to authorize
/// an on-chain item swap operation by a specific on-chain account.
///
/// NOTE: The signature is not part of the struct.
#[derive(Encode, Decode, Clone, PartialEq, RuntimeDebug, TypeInfo)]
#[codec(dumb_trait_bound)]
pub struct SwapOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId> {
	/// Swap item from collection id.
	pub collection_from_id: CollectionId,
	/// An item id to swap.
	pub item_from_id: ItemId,
	/// Swap to an item from specific collection id.
	pub collection_to_id: CollectionId,
	/// An item id to swap for. If `None` then any item from a specified collection would suit.
	pub item_to_id: Option<ItemId>,
	/// An optional price for the swap operation.
	pub price: Option<Balance>,
	/// A block number this is offer is valid until
	pub deadline: Option<BlockNumber>,
	/// Restrict this offer to a specific `item_to` owner.
	pub item_to_owner: AccountId,
	/// Off-chain offer's signer (an owner of `item_from`).
	pub signer: MultiSigner,
	/// An account that will receive an `item_from`.
	pub item_from_receiver: AccountId,
}

impl<CollectionId, ItemId, Balance, BlockNumber, AccountId>
	BuyOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId>
where
	BuyOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId>: Encode,
{
	/// Returns whether `signature` is a valid signature for this Offer
	/// and was created by the signer.
	pub fn verify(&self, signature: &MultiSignature) -> bool {
		let data = Encode::encode(&self);
		signature.verify(&*data, &self.signer.clone().into_account())
	}
}

impl<CollectionId, ItemId, Balance, BlockNumber, AccountId>
	SwapOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId>
where
	SwapOffer<CollectionId, ItemId, Balance, BlockNumber, AccountId>: Encode,
{
	/// Returns whether `signature` is a valid signature for this Offer
	/// and was created by the signer.
	pub fn verify(&self, signature: &MultiSignature) -> bool {
		let data = Encode::encode(&self);
		signature.verify(&*data, &self.signer.clone().into_account())
	}
}

impl<ItemId, Account, Balance> Collection<ItemId, Account, Balance> {
	pub fn destroy_witness(&self) -> DestroyWitness {
		DestroyWitness {
			items: self.items,
			item_metadatas: self.item_metadatas,
			attributes: self.attributes,
		}
	}
}

/// Represents either a System currency or a set of fungible assets.
#[derive(Encode, Decode, Clone, PartialEq, RuntimeDebug, TypeInfo)]
pub enum BalanceOrAsset<Balance, AssetId, AssetBalance> {
	Balance { amount: Balance },
	Asset { id: AssetId, amount: AssetBalance },
}

impl<B, A, AB> BalanceOrAsset<B, A, AB>
where
	B: core::cmp::PartialOrd,
{
	pub fn is_greater_or_equal(&self, other: &Self) -> bool {
		use BalanceOrAsset::*;
		match (self, other) {
			(Balance { amount: a }, Balance { amount: b }) => a >= b,
			_ => false,
		}
	}
}
