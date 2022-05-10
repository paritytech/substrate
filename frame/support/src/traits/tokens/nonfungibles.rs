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

//! Traits for dealing with multiple collections of non-fungible assets.
//!
//! This assumes a dual-level namespace identified by `Inspect::AssetId`, and could
//! reasonably be implemented by pallets which want to expose multiple independent collections of
//! NFT-like objects.
//!
//! For an NFT API which has single-level namespacing, the traits in `nonfungible` are better to
//! use.
//!
//! Implementations of these traits may be converted to implementations of corresponding
//! `nonfungible` traits by using the `nonfungible::ItemOf` type adapter.

use crate::dispatch::{DispatchError, DispatchResult};
use codec::{Decode, Encode};
use sp_runtime::TokenError;
use sp_std::prelude::*;

/// Trait for providing an interface to many read-only NFT-like sets of assets.
pub trait Inspect<AccountId> {
	/// Type for identifying an asset.
	type AssetId;

	/// Type for identifying an assets collection (an identifier for an independent collection of
	/// assets).
	type CollectionId;

	/// Returns the owner of `asset` of `collection`, or `None` if the asset doesn't exist
	/// (or somehow has no owner).
	fn owner(collection: &Self::CollectionId, asset: &Self::AssetId) -> Option<AccountId>;

	/// Returns the owner of the `collection`, if there is one. For many NFTs this may not
	/// make any sense, so users of this API should not be surprised to find an assets collection
	/// results in `None` here.
	fn collection_owner(_collection: &Self::CollectionId) -> Option<AccountId> {
		None
	}

	/// Returns the attribute value of `asset` of `collection` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(
		_collection: &Self::CollectionId,
		_asset: &Self::AssetId,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `asset` of `collection` corresponding to
	/// `key`.
	///
	/// By default this just attempts to use `attribute`.
	fn typed_attribute<K: Encode, V: Decode>(
		collection: &Self::CollectionId,
		asset: &Self::AssetId,
		key: &K,
	) -> Option<V> {
		key.using_encoded(|d| Self::attribute(collection, asset, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns the attribute value of `collection` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn collection_attribute(_collection: &Self::CollectionId, _key: &[u8]) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `collection` corresponding to `key`.
	///
	/// By default this just attempts to use `collection_attribute`.
	fn typed_collection_attribute<K: Encode, V: Decode>(
		collection: &Self::CollectionId,
		key: &K,
	) -> Option<V> {
		key.using_encoded(|d| Self::collection_attribute(collection, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns `true` if the `asset` of `collection` may be transferred.
	///
	/// Default implementation is that all assets are transferable.
	fn can_transfer(_collection: &Self::CollectionId, _asset: &Self::AssetId) -> bool {
		true
	}
}

/// Interface for enumerating assets in existence or owned by a given account over many collections
/// of NFTs.
pub trait InspectEnumerable<AccountId>: Inspect<AccountId> {
	/// Returns an iterator of the assets collections in existence.
	fn collections() -> Box<dyn Iterator<Item = Self::CollectionId>>;

	/// Returns an iterator of the assets of a `collection` in existence.
	fn assets(collection: &Self::CollectionId) -> Box<dyn Iterator<Item = Self::AssetId>>;

	/// Returns an iterator of the assets of all collections owned by `who`.
	fn owned(who: &AccountId) -> Box<dyn Iterator<Item = (Self::CollectionId, Self::AssetId)>>;

	/// Returns an iterator of the assets of `collection` owned by `who`.
	fn owned_in_collection(
		collection: &Self::CollectionId,
		who: &AccountId,
	) -> Box<dyn Iterator<Item = Self::AssetId>>;
}

/// Trait for providing the ability to create collections of nonfungible assets.
pub trait Create<AccountId>: Inspect<AccountId> {
	/// Create a `collection` of nonfungible assets to be owned by `who` and managed by `admin`.
	fn create_collection(
		collection: &Self::CollectionId,
		who: &AccountId,
		admin: &AccountId,
	) -> DispatchResult;
}

/// Trait for providing the ability to destroy collections of nonfungible assets.
pub trait Destroy<AccountId>: Inspect<AccountId> {
	/// The witness data needed to destroy an asset.
	type DestroyWitness;

	/// Provide the appropriate witness data needed to destroy an asset.
	fn get_destroy_witness(collection: &Self::CollectionId) -> Option<Self::DestroyWitness>;

	/// Destroy an existing fungible asset.
	/// * `collection`: The `CollectionId` to be destroyed.
	/// * `witness`: Any witness data that needs to be provided to complete the operation
	///   successfully.
	/// * `maybe_check_owner`: An optional account id that can be used to authorize the destroy
	///   command. If not provided, we will not do any authorization checks before destroying the
	///   asset.
	///
	/// If successful, this function will return the actual witness data from the destroyed asset.
	/// This may be different than the witness data provided, and can be used to refund weight.
	fn destroy(
		collection: Self::CollectionId,
		witness: Self::DestroyWitness,
		maybe_check_owner: Option<AccountId>,
	) -> Result<Self::DestroyWitness, DispatchError>;
}

/// Trait for providing an interface for multiple collections of NFT-like assets which may be
/// minted, burned and/or have attributes set on them.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Mint some `asset` of `collection` to be owned by `who`.
	///
	/// By default, this is not a supported operation.
	fn mint_into(
		_collection: &Self::CollectionId,
		_asset: &Self::AssetId,
		_who: &AccountId,
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Burn some `asset` of `collection`.
	///
	/// By default, this is not a supported operation.
	fn burn(
		_collection: &Self::CollectionId,
		_asset: &Self::AssetId,
		_maybe_check_owner: Option<&AccountId>,
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Set attribute `value` of `asset` of `collection`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_attribute(
		_collection: &Self::CollectionId,
		_asset: &Self::AssetId,
		_key: &[u8],
		_value: &[u8],
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `asset` of `collection`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_attribute<K: Encode, V: Encode>(
		collection: &Self::CollectionId,
		asset: &Self::AssetId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_attribute(collection, asset, k, v)))
	}

	/// Set attribute `value` of `collection`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_collection_attribute(
		_collection: &Self::CollectionId,
		_key: &[u8],
		_value: &[u8],
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `collection`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_collection_attribute<K: Encode, V: Encode>(
		collection: &Self::CollectionId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| {
			value.using_encoded(|v| Self::set_collection_attribute(collection, k, v))
		})
	}
}

/// Trait for providing a non-fungible sets of assets which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer `asset` of `collection` into `destination` account.
	fn transfer(
		collection: &Self::CollectionId,
		asset: &Self::AssetId,
		destination: &AccountId,
	) -> DispatchResult;
}
