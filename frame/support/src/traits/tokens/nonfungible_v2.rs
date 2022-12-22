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

//! Traits for dealing with a single non-fungible item.
//!
//! This assumes a single-level namespace identified by `Inspect::ItemId`, and could
//! reasonably be implemented by pallets that want to expose a single collection of NFT-like
//! objects.
//!
//! For an NFT API that has dual-level namespacing, the traits in `nonfungibles` are better to
//! use.

use super::nonfungibles_v2 as nonfungibles;
use crate::{
	dispatch::DispatchResult,
	traits::{tokens::misc::AttributeNamespace, Get},
};
use codec::{Decode, Encode};
use sp_runtime::TokenError;
use sp_std::prelude::*;

/// Trait for providing an interface to a read-only NFT-like item.
pub trait Inspect<AccountId> {
	/// Type for identifying an item.
	type ItemId;

	/// Returns the owner of `item`, or `None` if the item doesn't exist or has no
	/// owner.
	fn owner(item: &Self::ItemId) -> Option<AccountId>;

	/// Returns the attribute value of `item` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(
		_item: &Self::ItemId,
		_namespace: &AttributeNamespace<AccountId>,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `item` corresponding to `key`.
	///
	/// By default this just attempts to use `attribute`.
	fn typed_attribute<K: Encode, V: Decode>(
		item: &Self::ItemId,
		namespace: &AttributeNamespace<AccountId>,
		key: &K,
	) -> Option<V> {
		key.using_encoded(|d| Self::attribute(item, namespace, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns `true` if the `item` may be transferred.
	///
	/// Default implementation is that all items are transferable.
	fn can_transfer(_item: &Self::ItemId) -> bool {
		true
	}
}

/// Interface for enumerating items in existence or owned by a given account over a collection
/// of NFTs.
pub trait InspectEnumerable<AccountId>: Inspect<AccountId> {
	/// The iterator type for [`Self::items`].
	type ItemsIterator: Iterator<Item = Self::ItemId>;
	/// The iterator type for [`Self::owned`].
	type OwnedIterator: Iterator<Item = Self::ItemId>;

	/// Returns an iterator of the items within a `collection` in existence.
	fn items() -> Self::ItemsIterator;

	/// Returns an iterator of the items of all collections owned by `who`.
	fn owned(who: &AccountId) -> Self::OwnedIterator;
}

/// Trait for providing an interface for NFT-like items which may be minted, burned and/or have
/// attributes set on them.
pub trait Mutate<AccountId, ItemConfig>: Inspect<AccountId> {
	/// Mint some `item` to be owned by `who`.
	///
	/// By default, this is not a supported operation.
	fn mint_into(
		_item: &Self::ItemId,
		_who: &AccountId,
		_config: &ItemConfig,
		_deposit_collection_owner: bool,
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Burn some `item`.
	///
	/// By default, this is not a supported operation.
	fn burn(_item: &Self::ItemId, _maybe_check_owner: Option<&AccountId>) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Set attribute `value` of `item`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_attribute(_item: &Self::ItemId, _key: &[u8], _value: &[u8]) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `item`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_attribute<K: Encode, V: Encode>(
		item: &Self::ItemId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_attribute(item, k, v)))
	}
}

/// Trait for transferring a non-fungible item.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer `item` into `destination` account.
	fn transfer(item: &Self::ItemId, destination: &AccountId) -> DispatchResult;
}

/// Convert a `nonfungibles` trait implementation into a `nonfungible` trait implementation by
/// identifying a single item.
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
	type ItemId = <F as nonfungibles::Inspect<AccountId>>::ItemId;
	fn owner(item: &Self::ItemId) -> Option<AccountId> {
		<F as nonfungibles::Inspect<AccountId>>::owner(&A::get(), item)
	}
	fn attribute(
		item: &Self::ItemId,
		namespace: &AttributeNamespace<AccountId>,
		key: &[u8],
	) -> Option<Vec<u8>> {
		<F as nonfungibles::Inspect<AccountId>>::attribute(&A::get(), item, namespace, key)
	}
	fn typed_attribute<K: Encode, V: Decode>(
		item: &Self::ItemId,
		namespace: &AttributeNamespace<AccountId>,
		key: &K,
	) -> Option<V> {
		<F as nonfungibles::Inspect<AccountId>>::typed_attribute(&A::get(), item, namespace, key)
	}
	fn can_transfer(item: &Self::ItemId) -> bool {
		<F as nonfungibles::Inspect<AccountId>>::can_transfer(&A::get(), item)
	}
}

impl<
		F: nonfungibles::InspectEnumerable<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> InspectEnumerable<AccountId> for ItemOf<F, A, AccountId>
{
	type ItemsIterator = <F as nonfungibles::InspectEnumerable<AccountId>>::ItemsIterator;
	type OwnedIterator =
		<F as nonfungibles::InspectEnumerable<AccountId>>::OwnedInCollectionIterator;

	fn items() -> Self::ItemsIterator {
		<F as nonfungibles::InspectEnumerable<AccountId>>::items(&A::get())
	}
	fn owned(who: &AccountId) -> Self::OwnedIterator {
		<F as nonfungibles::InspectEnumerable<AccountId>>::owned_in_collection(&A::get(), who)
	}
}

impl<
		F: nonfungibles::Mutate<AccountId, ItemConfig>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
		ItemConfig,
	> Mutate<AccountId, ItemConfig> for ItemOf<F, A, AccountId>
{
	fn mint_into(
		item: &Self::ItemId,
		who: &AccountId,
		config: &ItemConfig,
		deposit_collection_owner: bool,
	) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId, ItemConfig>>::mint_into(
			&A::get(),
			item,
			who,
			config,
			deposit_collection_owner,
		)
	}
	fn burn(item: &Self::ItemId, maybe_check_owner: Option<&AccountId>) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId, ItemConfig>>::burn(&A::get(), item, maybe_check_owner)
	}
	fn set_attribute(item: &Self::ItemId, key: &[u8], value: &[u8]) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId, ItemConfig>>::set_attribute(
			&A::get(),
			item,
			key,
			value,
		)
	}
	fn set_typed_attribute<K: Encode, V: Encode>(
		item: &Self::ItemId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId, ItemConfig>>::set_typed_attribute(
			&A::get(),
			item,
			key,
			value,
		)
	}
}

impl<
		F: nonfungibles::Transfer<AccountId>,
		A: Get<<F as nonfungibles::Inspect<AccountId>>::CollectionId>,
		AccountId,
	> Transfer<AccountId> for ItemOf<F, A, AccountId>
{
	fn transfer(item: &Self::ItemId, destination: &AccountId) -> DispatchResult {
		<F as nonfungibles::Transfer<AccountId>>::transfer(&A::get(), item, destination)
	}
}
