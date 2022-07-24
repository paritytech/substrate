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

pub use crate::sp_io::{KillStorageResult, MultiRemovalResults};
use crate::{
	storage::{self, unhashed, StorageAppend},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec};

/// Generator for `StorageValue` used by `decl_storage`.
///
/// By default value is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait ChildTrie<T: FullCodec> {
	/// The type that get/take returns.
	type Query;

	fn get<T>() -> Option<T> {}

	fn get_or_default<T>() -> T {}

	fn get_or<T>() -> T {}

	fn get_or_else<T>() -> T {}

	fn put<T>() {}

	fn take<T>() -> Option<T> {}

	fn take_or_default<T>() -> T {}

	fn take_or<T>() -> T {}

	fn take_or_else<T>() -> T {}

	fn exists() -> bool {}

	fn clear_storage() -> MultiRemovalResults {}

	fn kill() {}

	fn get_raw() -> Option<Vec<u8>> {}

	fn put_raw() {}

	fn root() -> Vec<u8> {}

	fn len() -> Option<u32> {}
}

impl<T: FullCodec, G: ChildTrie<T>> storage::ChildTrie<T> for G {
	type Query = G::Query;

	fn get<T>() -> Option<T> {}

	fn get_or_default<T>() -> T {}

	fn get_or<T>() -> T {}

	fn get_or_else<T>() -> T {}

	fn put<T>() {}

	fn take<T>() -> Option<T> {}

	fn take_or_default<T>() -> T {}

	fn take_or<T>() -> T {}

	fn take_or_else<T>() -> T {}

	fn exists() -> bool {}

	fn clear_storage() -> MultiRemovalResults {}

	fn kill() {}

	fn get_raw() -> Option<Vec<u8>> {}

	fn put_raw() {}

	fn root() -> Vec<u8> {}

	fn len() -> Option<u32> {}
}
