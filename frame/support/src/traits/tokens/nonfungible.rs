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

//! Traits for dealing with a single non-fungible asset class.
//!
//! This assumes a single level namespace identified by `Inspect::InstanceId`, and could
//! reasonably be implemented by pallets which wants to expose a single collection of NFT-like
//! objects.
//!
//! For an NFT API which has dual-level namespacing, the traits in `nonfungibles` are better to
//! use.

use codec::{Encode, Decode};
use sp_std::prelude::*;
use sp_runtime::TokenError;
use crate::dispatch::DispatchResult;
use crate::traits::Get;
use super::nonfungibles;

/// Trait for providing an interface to a read-only NFT-like set of asset instances.
pub trait Inspect<AccountId> {
	/// Type for identifying an asset instance.
	type InstanceId;

	/// Returns the owner of asset `instance`, or `None` if the asset doesn't exist or has no
	/// owner.
	fn owner(instance: &Self::InstanceId) -> Option<AccountId>;

	/// Returns the attribute value of `instance` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(_instance: &Self::InstanceId, _key: &[u8]) -> Option<Vec<u8>> { None }

	/// Returns the strongly-typed attribute value of `instance` corresponding to `key`.
	///
	/// By default this just attempts to use `attribute`.
	fn typed_attribute<K: Encode, V: Decode>(instance: &Self::InstanceId, key: &K) -> Option<V> {
		key.using_encoded(|d| Self::attribute(instance, d))
			.and_then(|v| V::decode(&mut &v[..]).ok())
	}

	/// Returns `true` if the asset `instance` may be transferred.
	///
	/// Default implementation is that all assets are transferable.
	fn can_transfer(_instance: &Self::InstanceId) -> bool { true }
}

/// Interface for enumerating assets in existence or owned by a given account over a collection
/// of NFTs.
///
/// WARNING: These may be a heavy operations. Do not use when execution time is limited.
pub trait InspectEnumerable<AccountId>: Inspect<AccountId> {
	/// Returns the instances of an asset `class` in existence.
	fn instances() -> Vec<Self::InstanceId>;

	/// Returns the asset instances of all classes owned by `who`.
	fn owned(who: &AccountId) -> Vec<Self::InstanceId>;
}

/// Trait for providing an interface for NFT-like assets which may be minted, burned and/or have
/// attributes set on them.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Mint some asset `instance` to be owned by `who`.
	///
	/// By default, this is not a supported operation.
	fn mint_into(_instance: &Self::InstanceId, _who: &AccountId) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Burn some asset `instance`.
	///
	/// By default, this is not a supported operation.
	fn burn_from(_instance: &Self::InstanceId) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Set attribute `value` of asset `instance`'s `key`.
	///
	/// By default, this is not a supported operation.
	fn set_attribute(_instance: &Self::InstanceId, _key: &[u8], _value: &[u8]) -> DispatchResult {
		Err(TokenError::Unsupported.into())
	}

	/// Attempt to set the strongly-typed attribute `value` of `instance`'s `key`.
	///
	/// By default this just attempts to use `set_attribute`.
	fn set_typed_attribute<K: Encode, V: Encode>(
		instance: &Self::InstanceId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| value.using_encoded(|v| Self::set_attribute(instance, k, v)))
	}
}

/// Trait for providing a non-fungible set of assets which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer asset `instance` into `destination` account.
	fn transfer(instance: &Self::InstanceId, destination: &AccountId) -> DispatchResult;
}

/// Convert a `fungibles` trait implementation into a `fungible` trait implementation by identifying
/// a single item.
pub struct ItemOf<
	F: nonfungibles::Inspect<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::ClassId>,
	AccountId,
>(
	sp_std::marker::PhantomData<(F, A, AccountId)>
);

impl<
	F: nonfungibles::Inspect<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::ClassId>,
	AccountId,
> Inspect<AccountId> for ItemOf<F, A, AccountId> {
	type InstanceId = <F as nonfungibles::Inspect<AccountId>>::InstanceId;
	fn owner(instance: &Self::InstanceId) -> Option<AccountId> {
		<F as nonfungibles::Inspect<AccountId>>::owner(&A::get(), instance)
	}
	fn attribute(instance: &Self::InstanceId, key: &[u8]) -> Option<Vec<u8>> {
		<F as nonfungibles::Inspect<AccountId>>::attribute(&A::get(), instance, key)
	}
	fn typed_attribute<K: Encode, V: Decode>(instance: &Self::InstanceId, key: &K) -> Option<V> {
		<F as nonfungibles::Inspect<AccountId>>::typed_attribute(&A::get(), instance, key)
	}
	fn can_transfer(instance: &Self::InstanceId) -> bool {
		<F as nonfungibles::Inspect<AccountId>>::can_transfer(&A::get(), instance)
	}
}

impl<
	F: nonfungibles::InspectEnumerable<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::ClassId>,
	AccountId,
> InspectEnumerable<AccountId> for ItemOf<F, A, AccountId> {
	fn instances() -> Vec<Self::InstanceId> {
		<F as nonfungibles::InspectEnumerable<AccountId>>::instances(&A::get())
	}
	fn owned(who: &AccountId) -> Vec<Self::InstanceId> {
		<F as nonfungibles::InspectEnumerable<AccountId>>::owned_in_class(&A::get(), who)
	}
}

impl<
	F: nonfungibles::Mutate<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::ClassId>,
	AccountId,
> Mutate<AccountId> for ItemOf<F, A, AccountId> {
	fn mint_into(instance: &Self::InstanceId, who: &AccountId) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::mint_into(&A::get(), instance, who)
	}
	fn burn_from(instance: &Self::InstanceId) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::burn_from(&A::get(), instance)
	}
	fn set_attribute(instance: &Self::InstanceId, key: &[u8], value: &[u8]) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::set_attribute(&A::get(), instance, key, value)
	}
	fn set_typed_attribute<K: Encode, V: Encode>(
		instance: &Self::InstanceId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		<F as nonfungibles::Mutate<AccountId>>::set_typed_attribute(&A::get(), instance, key, value)
	}
}

impl<
	F: nonfungibles::Transfer<AccountId>,
	A: Get<<F as nonfungibles::Inspect<AccountId>>::ClassId>,
	AccountId,
> Transfer<AccountId> for ItemOf<F, A, AccountId> {
	fn transfer(instance: &Self::InstanceId, destination: &AccountId) -> DispatchResult {
		<F as nonfungibles::Transfer<AccountId>>::transfer(&A::get(), instance, destination)
	}
}
