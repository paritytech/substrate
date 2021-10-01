// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
//! This assumes a dual-level namespace identified by `Inspect::InstanceId`, and could
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

/// Trait for providing an interface to many read-only NFT-like sets of asset instances.
pub trait Inspect<AccountId> {
	/// Type for identifying an asset instance.
	type InstanceId;

	/// Type for identifying an asset class (an identifier for an independent collection of asset
	/// instances).
	type ClassId;

	/// Returns the owner of asset `instance` of `class`, or `None` if the asset doesn't exist (or
	/// somehow has no owner).
	fn owner(class: &Self::ClassId, instance: &Self::InstanceId) -> Option<AccountId>;

	/// Returns the owner of the asset `class`, if there is one. For many NFTs this may not make
	/// any sense, so users of this API should not be surprised to find an asset class results in
	/// `None` here.
	fn class_owner(_class: &Self::ClassId) -> Option<AccountId> {
		None
	}

	/// Returns the attribute value of `instance` of `class` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(
		_class: &Self::ClassId,
		_instance: &Self::InstanceId,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `instance` of `class` corresponding to `key`.
	///
	/// By default this just attempts to use `attribute`.
	fn typed_attribute<K: Encode, V: Decode>(
		class: &Self::ClassId,
		instance: &Self::InstanceId,
		key: &K,
	) -> Option<V> {
		key.using_encoded(|d| Self::attribute(class, instance, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns the attribute value of `class` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn class_attribute(_class: &Self::ClassId, _key: &[u8]) -> Option<Vec<u8>> {
		None
	}

	/// Returns the strongly-typed attribute value of `class` corresponding to `key`.
	///
	/// By default this just attempts to use `class_attribute`.
	fn typed_class_attribute<K: Encode, V: Decode>(class: &Self::ClassId, key: &K) -> Option<V> {
		key.using_encoded(|d| Self::class_attribute(class, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns `true` if the asset `instance` of `class` may be transferred.
	///
	/// Default implementation is that all assets are transferable.
	fn can_transfer(_class: &Self::ClassId, _instance: &Self::InstanceId) -> bool {
		true
	}
}

/// Interface for enumerating assets in existence or owned by a given account over many collections
/// of NFTs.
pub trait InspectEnumerable<AccountId>: Inspect<AccountId> {
	/// Returns an iterator of the asset classes in existence.
	fn classes() -> Box<dyn Iterator<Item = Self::ClassId>>;

	/// Returns an iterator of the instances of an asset `class` in existence.
	fn instances(class: &Self::ClassId) -> Box<dyn Iterator<Item = Self::InstanceId>>;

	/// Returns an iterator of the asset instances of all classes owned by `who`.
	fn owned(who: &AccountId) -> Box<dyn Iterator<Item = (Self::ClassId, Self::InstanceId)>>;

	/// Returns an iterator of the asset instances of `class` owned by `who`.
	fn owned_in_class(
		class: &Self::ClassId,
		who: &AccountId,
	) -> Box<dyn Iterator<Item = Self::InstanceId>>;
}

/// Trait for providing the ability to create classes of nonfungible assets.
pub trait Create<AccountId>: Inspect<AccountId> {
	/// Create a `class` of nonfungible assets to be owned by `who` and managed by `admin`.
	fn create_class(class: &Self::ClassId, who: &AccountId, admin: &AccountId) -> DispatchResult;
}

/// Trait for providing the ability to destroy classes of nonfungible assets.
pub trait Destroy<AccountId>: Inspect<AccountId> {
	/// The witness data needed to destroy an asset.
	type DestroyWitness;

	/// Provide the appropriate witness data needed to destroy an asset.
	fn get_destroy_witness(class: &Self::ClassId) -> Option<Self::DestroyWitness>;

	/// Destroy an existing fungible asset.
	/// * `class`: The `ClassId` to be destroyed.
	/// * `witness`: Any witness data that needs to be provided to complete the operation
	///   successfully.
	/// * `maybe_check_owner`: An optional account id that can be used to authorize the destroy
	///   command. If not provided, we will not do any authorization checks before destroying the
	///   asset.
	///
	/// If successful, this function will return the actual witness data from the destroyed asset.
	/// This may be different than the witness data provided, and can be used to refund weight.
	fn destroy(
		class: Self::ClassId,
		witness: Self::DestroyWitness,
		maybe_check_owner: Option<AccountId>,
	) -> Result<Self::DestroyWitness, DispatchError>;
}

/// Trait for providing an interface for multiple classes of NFT-like assets which may be minted,
/// burned and/or have attributes set on them.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Mint some asset `instance` of `class` to be owned by `who`.
	///
	/// By default, this is not a supported operation.
	fn mint_into(
		_class: &Self::ClassId,
		_instance: &Self::InstanceId,
		_who: &AccountId,
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Burn some asset `instance` of `class`.
	///
	/// By default, this is not a supported operation.
	fn burn_from(_class: &Self::ClassId, _instance: &Self::InstanceId) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Set attribute `value` of asset `instance` of `class`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_attribute(
		_class: &Self::ClassId,
		_instance: &Self::InstanceId,
		_key: &[u8],
		_value: &[u8],
	) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `instance` of `class`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_attribute<K: Encode, V: Encode>(
		class: &Self::ClassId,
		instance: &Self::InstanceId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_attribute(class, instance, k, v)))
	}

	/// Set attribute `value` of asset `class`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_class_attribute(_class: &Self::ClassId, _key: &[u8], _value: &[u8]) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `class`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_class_attribute<K: Encode, V: Encode>(
		class: &Self::ClassId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_class_attribute(class, k, v)))
	}
}

/// Trait for providing a non-fungible sets of assets which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer asset `instance` of `class` into `destination` account.
	fn transfer(
		class: &Self::ClassId,
		instance: &Self::InstanceId,
		destination: &AccountId,
	) -> DispatchResult;
}
