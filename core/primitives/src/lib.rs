// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Shareable Substrate types.

#![warn(missing_docs)]

#![cfg_attr(not(feature = "std"), no_std)]

/// Initialize a key-value collection from array.
///
/// Creates a vector of given pairs and calls `collect` on the iterator from it.
/// Can be used to create a `HashMap`.
#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

use rstd::prelude::*;
use rstd::ops::Deref;
use parity_codec::{Encode, Decode};
#[cfg(feature = "std")]
use std::borrow::Cow;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};

#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;

#[cfg(feature = "std")]
pub mod hashing;
#[cfg(feature = "std")]
pub use hashing::{blake2_128, blake2_256, twox_64, twox_128, twox_256};
#[cfg(feature = "std")]
pub mod hexdisplay;
pub mod crypto;

pub mod u32_trait;

pub mod ed25519;
pub mod sr25519;
pub mod hash;
mod hasher;
pub mod sandbox;
pub mod storage;
pub mod uint;
mod changes_trie;

#[cfg(test)]
mod tests;

pub use self::hash::{H160, H256, H512, convert_hash};
pub use self::uint::U256;
pub use changes_trie::ChangesTrieConfiguration;
#[cfg(feature = "std")]
pub use crypto::{DeriveJunction, Pair};

pub use hash_db::Hasher;
// Switch back to Blake after PoC-3 is out
// pub use self::hasher::blake::BlakeHasher;
pub use self::hasher::blake2::Blake2Hasher;

/// Context for executing a call into the runtime.
#[repr(u8)]
pub enum ExecutionContext {
	/// Context for general importing (including own blocks).
	Importing,
	/// Context used when syncing the blockchain.
	Syncing,
	/// Context used for block construction.
	BlockConstruction,
	/// Offchain worker context.
	OffchainWorker(Box<OffchainExt>),
	/// Context used for other calls.
	Other,
}

/// An extended externalities for offchain workers.
pub trait OffchainExt {
	/// Submits an extrinsics.
	///
	/// The extrinsic will either go to the pool (signed)
	/// or to the next produced block (inherent).
	fn submit_extrinsic(&mut self, extrinsic: Vec<u8>);
}
impl<T: OffchainExt + ?Sized> OffchainExt for Box<T> {
	fn submit_extrinsic(&mut self, ex: Vec<u8>) {
		(&mut **self).submit_extrinsic(ex)
	}
}

/// Hex-serialized shim for `Vec<u8>`.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord))]
pub struct Bytes(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl From<Vec<u8>> for Bytes {
	fn from(s: Vec<u8>) -> Self { Bytes(s) }
}

impl From<OpaqueMetadata> for Bytes {
	fn from(s: OpaqueMetadata) -> Self { Bytes(s.0) }
}

impl Deref for Bytes {
	type Target = [u8];
	fn deref(&self) -> &[u8] { &self.0[..] }
}

/// Stores the encoded `RuntimeMetadata` for the native side as opaque type.
#[derive(Encode, Decode, PartialEq)]
pub struct OpaqueMetadata(Vec<u8>);

impl OpaqueMetadata {
	/// Creates a new instance with the given metadata blob.
	pub fn new(metadata: Vec<u8>) -> Self {
		OpaqueMetadata(metadata)
	}
}

impl rstd::ops::Deref for OpaqueMetadata {
	type Target = Vec<u8>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

/// Something that is either a native or an encoded value.
#[cfg(feature = "std")]
pub enum NativeOrEncoded<R> {
	/// The native representation.
	Native(R),
	/// The encoded representation.
	Encoded(Vec<u8>)
}

#[cfg(feature = "std")]
impl<R: parity_codec::Encode> ::std::fmt::Debug for NativeOrEncoded<R> {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		self.as_encoded().as_ref().fmt(f)
	}
}

#[cfg(feature = "std")]
impl<R: parity_codec::Encode> NativeOrEncoded<R> {
	/// Return the value as the encoded format.
	pub fn as_encoded<'a>(&'a self) -> Cow<'a, [u8]> {
		match self {
			NativeOrEncoded::Encoded(e) => Cow::Borrowed(e.as_slice()),
			NativeOrEncoded::Native(n) => Cow::Owned(n.encode()),
		}
	}

	/// Return the value as the encoded format.
	pub fn into_encoded(self) -> Vec<u8> {
		match self {
			NativeOrEncoded::Encoded(e) => e,
			NativeOrEncoded::Native(n) => n.encode(),
		}
	}
}

#[cfg(feature = "std")]
impl<R: PartialEq + parity_codec::Decode> PartialEq for NativeOrEncoded<R> {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(NativeOrEncoded::Native(l), NativeOrEncoded::Native(r)) => l == r,
			(NativeOrEncoded::Native(n), NativeOrEncoded::Encoded(e)) |
			(NativeOrEncoded::Encoded(e), NativeOrEncoded::Native(n)) =>
				Some(n) == parity_codec::Decode::decode(&mut &e[..]).as_ref(),
			(NativeOrEncoded::Encoded(l), NativeOrEncoded::Encoded(r)) => l == r,
		}
	}
}

/// A value that is never in a native representation.
/// This is type is useful in conjuction with `NativeOrEncoded`.
#[cfg(feature = "std")]
#[derive(PartialEq)]
pub enum NeverNativeValue {}

#[cfg(feature = "std")]
impl parity_codec::Encode for NeverNativeValue {
	fn encode(&self) -> Vec<u8> {
		// The enum is not constructable, so this function should never be callable!
		unreachable!()
	}
}

#[cfg(feature = "std")]
impl parity_codec::Decode for NeverNativeValue {
	fn decode<I: parity_codec::Input>(_: &mut I) -> Option<Self> {
		None
	}
}
