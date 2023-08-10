// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Traits and types for non-continous storage types (lists).

use codec::{EncodeLike, FullCodec};

/// A non-continuous container type that can only be iterated.
pub trait StorageList<V: FullCodec> {
	/// Iterator for normal and draining iteration.
	type Iterator: Iterator<Item = V>;

	/// Append iterator for fast append operations.
	type Appender: StorageListAppender<V>;

	/// Number of elements in the list.
	fn len() -> u64;

	/// List the elements in append order.
	fn iter() -> Self::Iterator;

	/// Drain the elements in append order.
	///
	/// Note that this drains a value as soon as it is being inspected. For example `take_while(|_|
	/// false)` still drains the first element. This also applies to `peek()`.
	fn drain() -> Self::Iterator;

	/// A fast append iterator.
	fn appender() -> Self::Appender;

	/// Append a single element.
	///
	/// Should not be called repeatedly; use `append_many` instead.  
	/// Worst case linear `O(len)` with `len` being the number if elements in the list.
	fn append_one<EncodeLikeValue>(item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<V>,
	{
		Self::append_many(core::iter::once(item));
	}

	/// Append many elements.
	///
	/// Should not be called repeatedly; use `appender` instead.  
	/// Worst case linear `O(len + items.count())` with `len` beings the number if elements in the
	/// list.
	fn append_many<EncodeLikeValue, I>(items: I)
	where
		EncodeLikeValue: EncodeLike<V>,
		I: IntoIterator<Item = EncodeLikeValue>,
	{
		let mut ap = Self::appender();
		ap.append_many(items);
	}
}

/// A non-continuous container type with a key that can only be iterated.
pub trait StorageKeyedList<K, V: FullCodec> {
	/// Iterator for normal and draining iteration.
	type Iterator: Iterator<Item = V>;

	/// Append iterator for fast append operations.
	type Appender: StorageListAppender<V>;

	/// Number of elements in the list.
	fn len(key: K) -> u64;

	/// List the elements in append order.
	fn iter(key: K) -> Self::Iterator;

	/// Drain the elements in append order.
	///
	/// Note that this drains a value as soon as it is being inspected. For example `take_while(|_|
	/// false)` still drains the first element. This also applies to `peek()`.
	fn drain(key: K) -> Self::Iterator;

	/// A fast append iterator.
	fn appender(key: K) -> Self::Appender;

	/// Append a single element.
	///
	/// Should not be called repeatedly; use `append_many` instead.  
	/// Worst case linear `O(len)` with `len` being the number if elements in the list.
	fn append_one<EncodeLikeValue>(key: K, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<V>,
	{
		Self::append_many(key, core::iter::once(item));
	}

	/// Append many elements.
	///
	/// Should not be called repeatedly; use `appender` instead.  
	/// Worst case linear `O(len + items.count())` with `len` beings the number if elements in the
	/// list.
	fn append_many<EncodeLikeValue, I>(key: K, items: I)
	where
		EncodeLikeValue: EncodeLike<V>,
		I: IntoIterator<Item = EncodeLikeValue>,
	{
		let mut ap = Self::appender(key);
		ap.append_many(items);
	}
}

/// Append iterator to append values to a storage struct.
///
/// Can be used in situations where appending does not have constant time complexity.
pub trait StorageListAppender<V: FullCodec> {
	/// Append a single item in constant time `O(1)`.
	fn append<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<V>;

	/// Append many items in linear time `O(items.count())`.
	// Note: a default impl is provided since `Self` is already assumed to be optimal for single
	// append operations.
	fn append_many<EncodeLikeValue, I>(&mut self, items: I)
	where
		EncodeLikeValue: EncodeLike<V>,
		I: IntoIterator<Item = EncodeLikeValue>,
	{
		for item in items.into_iter() {
			self.append(item);
		}
	}
}
