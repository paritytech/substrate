// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for the FRAME NFTs pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::dispatch::Vec;

sp_api::decl_runtime_apis! {
	pub trait NftsApi<AccountId, CollectionId, ItemId>
	where
		AccountId: Encode + Decode,
		CollectionId: Encode,
		ItemId: Encode,
	{
		fn owner(collection: CollectionId, item: ItemId) -> Option<AccountId>;

		fn collection_owner(collection: CollectionId) -> Option<AccountId>;

		fn attribute(
			collection: CollectionId,
			item: ItemId,
			key: Vec<u8>,
		) -> Option<Vec<u8>>;

		fn custom_attribute(
			account: AccountId,
			collection: CollectionId,
			item: ItemId,
			key: Vec<u8>,
		) -> Option<Vec<u8>>;

		fn system_attribute(
			collection: CollectionId,
			item: ItemId,
			key: Vec<u8>,
		) -> Option<Vec<u8>>;

		fn collection_attribute(collection: CollectionId, key: Vec<u8>) -> Option<Vec<u8>>;
	}
}
