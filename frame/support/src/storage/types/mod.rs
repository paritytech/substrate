// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Storage types to build abstraction on storage, they implements storage traits such as
//! StorageMap and others.

use codec::FullCodec;
use frame_metadata::{DefaultByte, StorageEntryModifier};

mod value;
mod map;
mod double_map;

pub use value::{StorageValue, StorageValueMetadata};
pub use map::{StorageMap, StorageMapMetadata};
pub use double_map::{StorageDoubleMap, StorageDoubleMapMetadata};

/// Trait implementing how the storage optional value is converted into the queried type.
///
/// It is implemented by:
/// * `OptionQuery` which convert an optional value to an optional value, user when querying
///   storage will get an optional value.
/// * `ValueQuery` which convert an optional value to a value, user when querying storage will get
///   a value.
pub trait QueryKindTrait<Value> {
	/// Metadata for the storage kind.
	const METADATA: StorageEntryModifier;

	/// Type returned on query
	type Query: FullCodec + 'static;

	/// Convert an optional value (i.e. some if trie contains the value or none otherwise) to the
	/// query.
	fn from_optional_value_to_query<OnEmpty>(v: Option<Value>) -> Self::Query where
		OnEmpty: crate::traits::Get<Self::Query>;

	/// Convert a query to an optional value.
	fn from_query_to_optional_value(v: Self::Query) -> Option<Value>;
}

/// Implement QueryKindTrait with query being `Option<Value>`
pub struct OptionQuery;
impl<Value: FullCodec + 'static> QueryKindTrait<Value> for OptionQuery {
	const METADATA: StorageEntryModifier = StorageEntryModifier::Optional;
	type Query = Option<Value>;
	fn from_optional_value_to_query<OnEmpty>(v: Option<Value>) -> Self::Query where
		OnEmpty: crate::traits::Get<Self::Query>
	{
		if v.is_none() {
			OnEmpty::get()
		} else {
			v
		}
	}
	fn from_query_to_optional_value(v: Self::Query) -> Option<Value> {
		v
	}
}

/// Implement QueryKindTrait with query being `Value`
pub struct ValueQuery;
impl<Value: FullCodec + 'static> QueryKindTrait<Value> for ValueQuery where
{
	const METADATA: StorageEntryModifier = StorageEntryModifier::Default;
	type Query = Value;
	fn from_optional_value_to_query<OnEmpty>(v: Option<Value>) -> Self::Query where
		OnEmpty: crate::traits::Get<Self::Query>
	{
		v.unwrap_or_else(|| OnEmpty::get())
	}
	fn from_query_to_optional_value(v: Self::Query) -> Option<Value> {
		Some(v)
	}
}

/// A helper struct which implements DefaultByte using `Get<Value>` and encode it.
struct OnEmptyGetter<Value, OnEmpty>(core::marker::PhantomData<(Value, OnEmpty)>);
impl<Value: FullCodec, OnEmpty: crate::traits::Get<Value>> DefaultByte
	for OnEmptyGetter<Value, OnEmpty>
{
	fn default_byte(&self) -> sp_std::vec::Vec<u8> {
		OnEmpty::get().encode()
	}
}
unsafe impl <Value, OnEmpty: crate::traits::Get<Value>> Send for OnEmptyGetter<Value, OnEmpty> {}
unsafe impl <Value, OnEmpty: crate::traits::Get<Value>> Sync for OnEmptyGetter<Value, OnEmpty> {}
