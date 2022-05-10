// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Traits for dealing with a single non-fungible assets collection.
//!
//! This assumes a single level namespace identified by `Inspect::AssetId`, and could
//! reasonably be implemented by pallets which wants to expose a single collection of NFT-like
//! objects.
//!
//! For an NFT API which has dual-level namespacing, the traits in `nonfungibles` are better to
//! use.

use super::nonfungibles;
use crate::{dispatch::DispatchResult, traits::Get};
use codec::{Decode, Encode};
use sp_runtime::TokenError;
use sp_std::prelude::*;

/// Trait for providing an interface to a read-only NFT-like set of assets.
pub trait Inspect<AccountId> {
	/// Type for identifying an asset.
	type AssetId;

	/// Returns the owner of asset `asset`, or `None` if the asset doesn't exist or has no
	/// owner.
	fn owner(asset: &Self::AssetId) -> Option<AccountId>;

	/// Returns the attribute value of `asset` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(_asset: &Self::AssetId, _key: &[u8]) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `asset` corresponding to `key`.
	///
	/// By default this just attempts to use `attribute`.
	fn typed_attribute<K: Encode, V: Decode>(asset: &Self::AssetId, key: &K) -> Option<V> {
		key.using_encoded(|d| Self::attribute(asset, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns `true` if the asset `asset` may be transferred.
	///
	/// Default implementation is that all assets are transferable.
	fn can_transfer(_asset: &Self::AssetId) -> bool {
		true
	}
}

/// Interface for enumerating assets in existence or owned by a given account over a collection
/// of NFTs.
pub trait InspectEnumerable<AccountId>: Inspect<AccountId> {
	/// Returns an iterator of the assets of an asset `collection` in existence.
	fn assets() -> Box<dyn Iterator<Item = Self::AssetId>>;

	/// Returns an iterator of the assets of all collections owned by `who`.
	fn owned(who: &AccountId) -> Box<dyn Iterator<Item = Self::AssetId>>;
}

/// Trait for providing an interface for NFT-like assets which may be minted, burned and/or have
/// attributes set on them.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Mint some asset `asset` to be owned by `who`.
	///
	/// By default, this is not a supported operation.
	fn mint_into(_asset: &Self::AssetId, _who: &AccountId) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Burn some asset `asset`.
	///
	/// By default, this is not a supported operation.
	fn burn(_asset: &Self::AssetId, _maybe_check_owner: Option<&AccountId>) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Set attribute `value` of asset `asset`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_attribute(_asset: &Self::AssetId, _key: &[u8], _value: &[u8]) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `asset`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_attribute<K: Encode, V: Encode>(
		asset: &Self::AssetId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_attribute(asset, k, v)))
	}
}

/// Trait for providing a non-fungible set of assets which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer asset `asset` into `destination` account.
	fn transfer(asset: &Self::AssetId, destination: &AccountId) -> DispatchResult;
}

/// Convert a `fungibles` trait implementation into a `fungible` trait implementation by identifying
/// a single item.
pub struct ItemOf<
	F: nonfungibles::Inspect<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
	AccountId,
>(sp_std::marker::PhantomData<(F, A, AccountId)>);

impl<
		F: nonfungibles::Inspect<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> Inspect<AccountId> for ItemOf<F, A, AccountId>
{
	type AssetId = <F as nonfungibles::Inspect<AccountId>>::AssetId;
	fn owner(asset: &Self::AssetId) -> Option<AccountId> {
		<F as nonfungibles::Inspect<AccountId>>::owner(&A::get(), asset)
	}
	fn attribute(asset: &Self::AssetId, key: &[u8]) -> Option<Vec<u8>> {
		<F as nonfungibles::Inspect<AccountId>>::attribute(&A::get(), asset, key)
	}
	fn typed_attribute<K: Encode, V: Decode>(asset: &Self::AssetId, key: &K) -> Option<V> {
		<F as nonfungibles::Inspect<AccountId>>::typed_attribute(&A::get(), asset, key)
	}
	fn can_transfer(asset: &Self::AssetId) -> bool {
		<F as nonfungibles::Inspect<AccountId>>::can_transfer(&A::get(), asset)
	}
}

impl<
		F: nonfungibles::InspectEnumerable<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> InspectEnumerable<AccountId> for ItemOf<F, A, AccountId>
{
	fn assets() -> Box<dyn Iterator<Item = Self::AssetId>> {
		<F as nonfungibles::InspectEnumerable<AccountId>>::assets(&A::get())
	}
	fn owned(who: &AccountId) -> Box<dyn Iterator<Item = Self::AssetId>> {
		<F as nonfungibles::InspectEnumerable<AccountId>>::owned_in_collection(&A::get(), who)
	}
}

impl<
		F: nonfungibles::Mutate<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> Mutate<AccountId> for ItemOf<F, A, AccountId>
{
	fn mint_into(asset: &Self::AssetId, who: &AccountId) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::mint_into(&A::get(), asset, who)
	}
	fn burn(asset: &Self::AssetId, maybe_check_owner: Option<&AccountId>) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::burn(&A::get(), asset, maybe_check_owner)
	}
	fn set_attribute(asset: &Self::AssetId, key: &[u8], value: &[u8]) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::set_attribute(&A::get(), asset, key, value)
	}
	fn set_typed_attribute<K: Encode, V: Encode>(
		asset: &Self::AssetId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::set_typed_attribute(&A::get(), asset, key, value)
	}
}

impl<
		F: nonfungibles::Transfer<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> Transfer<AccountId> for ItemOf<F, A, AccountId>
{
	fn transfer(asset: &Self::AssetId, destination: &AccountId) -> DispatchResult {
		<F as nonfungibles::Transfer<AccountId>>::transfer(&A::get(), asset, destination)
	}
}
