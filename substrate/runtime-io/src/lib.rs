// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! This is part of the Substrate runtime.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#![cfg_attr(feature = "std", doc = "Substrate runtime standard library as compiled when linked with Rust's standard library.")]
#![cfg_attr(not(feature = "std"), doc = "Substrate's runtime standard library as compiled without Rust's standard library.")]

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

/// Abstraction around hashing
pub trait Hashing {
	/// The hash type produced.
	type Output;

	/// Produce the hash of some byte-slice.
	fn hash(s: &[u8]) -> Self::Output;
	/// Produce the hash of some codec-encodable value.
	fn hash_of<S: codec::Slicable>(s: &S) -> Self::Output {
		codec::Slicable::using_encoded(s, Self::hash)
	}
	/// Produce the patricia-trie root of a mapping from indices to byte slices.
	fn enumerated_trie_root(items: &[&[u8]]) -> Self::Output;

	/// Acquire the global storage root.
	fn storage_root() -> Self::Output;
}

/// Blake2-256 Hashing implementation.
pub struct BlakeTwo256;

impl Hashing for BlakeTwo256 {
	type Output = primitives::H256;
	fn hash(s: &[u8]) -> Self::Output {
		blake2_256(s).into()
	}
	fn enumerated_trie_root(items: &[&[u8]]) -> Self::Output {
		enumerated_trie_root(items).into()
	}
	fn storage_root() -> Self::Output {
		storage_root().into()
	}
}
