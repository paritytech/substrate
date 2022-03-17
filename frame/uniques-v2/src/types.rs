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
use enumflags2::{bitflags, BitFlag, BitFlags};
use frame_support::RuntimeDebug;
use scale_info::TypeInfo;

// Support for up to 64 user-enabled features on a collection.
#[bitflags]
#[repr(u64)]
#[derive(Copy, Clone, RuntimeDebug, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum UserFeatures {
	Administration,
	Royalty,
	Limited,
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
pub struct Collection<CollectionId, Account, Balance, Metadata> {
	pub id: CollectionId,
	pub owner: Account,
	pub deposit: Balance,
	pub metadata: Metadata,
}

#[derive(Encode, Decode, PartialEq, Default, MaxEncodedLen, TypeInfo)]
pub struct Item<ItemId, Account, Balance, Metadata> {
	pub id: ItemId,
	pub owner: Account,
	pub deposit: Balance,
	pub metadata: Metadata,
}
