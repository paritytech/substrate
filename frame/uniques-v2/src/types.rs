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
use enumflags2::{bitflags};
use frame_support::RuntimeDebug;
use scale_info::TypeInfo;

// Support for up to 64 user-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum UserFeatures {
	Administration,
	Royalty,
	IsLocked,
	NonTransferableItems,
}

// Support for up to 64 system-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum SystemFeatures {
	NoDeposit,
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
	pub owner: Account,
	pub deposit: Option<Balance>,
	pub attributes: u32,
	pub items: u32,
	pub item_metadatas: u32,
	pub max_supply: Option<u32>,
	pub max_items_per_account: Option<u32>,
}

#[derive(Encode, Decode, PartialEq, Default, MaxEncodedLen, TypeInfo)]
pub struct Item<ItemId, Account, Balance> {
	pub id: ItemId,
	pub owner: Account,
	pub deposit: Option<Balance>,
	// `None` assumes not for sale
	pub price: Option<Balance>,
	// `None` assumes anyone can buy
	pub buyer: Option<Account>,
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

impl<ItemId, Account, Balance> Collection<ItemId, Account, Balance> {
	pub fn destroy_witness(&self) -> DestroyWitness {
		DestroyWitness {
			items: self.items,
			item_metadatas: self.item_metadatas,
			attributes: self.attributes,
		}
	}
}
