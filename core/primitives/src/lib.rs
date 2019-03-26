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
#![cfg_attr(not(feature = "std"), feature(alloc))]

/// Initalise a key-value collection from array.
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
use serde_derive::{Serialize, Deserialize};

#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;

#[cfg(feature = "std")]
pub mod hashing;
#[cfg(feature = "std")]
pub use hashing::{blake2_256, twox_128, twox_256};
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

/// Hex-serialised shim for `Vec<u8>`.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord))]
pub struct Bytes(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

// use prefixed key for keyspace TODO put keyspace support at KeyValueDB level
// TODO for default impl in kvdb run a hashing first?? -> warn to keep key for no ks (some
// test code is accessing directly the db over the memorydb key!!
// Note that this scheme must produce new key same as old key if ks is the empty vec
// TODO put it as inner SubTrie function (requires changing child trie proto first)
// TODO switch to simple mixing until trie pr changing Hashdb get merged (not even prefixed)
pub fn keyspace_as_prefix<H: AsRef<[u8]>>(ks: &KeySpace, key: &H, dst: &mut[u8]) {
	assert!(dst.len() == keyspace_expected_len(ks, key));
	//dst[..ks.len()].copy_from_slice(&ks[..]);
	dst[ks.len()..].copy_from_slice(key.as_ref());
	let high = ::rstd::cmp::min(ks.len(), key.as_ref().len());
	// TODO this mixing will be useless after trie pr merge (keeping it until then)
	// same thing we use H dest but not after pr merge
	//let start = ks.len();
	let start = 0;
	for (k, a) in dst[ks.len()..high].iter_mut().zip(key.as_ref()[..high].iter()) {
	//for (k, a) in dst[ks.len()..high].iter_mut().zip(key.as_ref()[..high].iter()) {
		// TODO any use of xor val? (preventing some targeted collision I would say)
		*k ^= *a;
	}
}

/// TODO when things work SubTrie will need to use key as param type, same for KeySpace
pub fn keyspace_expected_len<H: AsRef<[u8]>>(ks: &KeySpace, key: &H) -> usize {
	//ks.len() + key.as_ref().len()
	key.as_ref().len()
}

/// keyspace as prefix with allocation
pub fn keyspace_as_prefix_alloc<H: AsRef<[u8]> + Clone + AsMut<[u8]>>(ks: &KeySpace, key: &H) -> H {
	//let mut res = Vec::with_capacity(keyspace_expected_len(ks, key));
	let mut res = key.clone();
	keyspace_as_prefix(ks, key, res.as_mut());
	res

}

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

/// keyspace type.
pub type KeySpace = Vec<u8>;


/// key of subtrie in parent trie.
pub type ParentTrie = Vec<u8>;

/// child trie stored definition
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord))]
pub struct SubTrieNode {
	/// subtrie unique keyspace
	#[cfg_attr(feature = "std", serde(with="bytes"))]
	pub keyspace: KeySpace,
	/// subtrie current root hash
	#[cfg_attr(feature = "std", serde(with="bytes"))]
	pub root: Vec<u8>,
}

/// child trie infos
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
pub struct SubTrie {
	/// subtrie node info
	pub node: SubTrieNode,
	/// subtrie path
	pub parent: ParentTrie,
}

impl SubTrie {
	/// instantiate new subtrie without root value
	pub fn new(keyspace: KeySpace, parent: ParentTrie) -> Self {
		SubTrie {
			node: SubTrieNode {
				keyspace,
				root: Default::default(),
			},
			parent,
		}
	}
	pub fn encoded_node(&self) -> Vec<u8> {
		parity_codec::Encode::encode(&self.node)
	}
}
