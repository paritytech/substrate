// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::{Layout, TrieLayout};
use codec::{Decode, Encode};
use hash_db::{HashDB, Hasher};
use sp_core::state_version::StateVersion;
use sp_std::vec::Vec;
use trie_db::NodeCodec;

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// The proof consists of the set of serialized nodes in the storage trie accessed when looking up
/// the keys covered by the proof. Verifying the proof requires constructing the partial trie from
/// the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone, Encode)]
pub struct StorageProof {
	// TODO decode no more bytes to V0 for compatibility  and remove pub(crate)
	pub(crate) trie_nodes: Vec<Vec<u8>>,
	pub(crate) state_version: StateVersion,
}

/// Storage proof in compact form.
#[derive(Debug, PartialEq, Eq, Clone, Encode)]
pub struct CompactProof {
	pub encoded_nodes: Vec<Vec<u8>>,
	pub state_version: StateVersion,
}

mod decode_impl {
	use super::*;
	use codec::{Error, Input};
	impl Decode for StorageProof {
		fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
			let trie_nodes: Vec<Vec<u8>> = Decode::decode(input)?;
			let state_version = if let Ok(Some(0)) = input.remaining_len() {
				// for compatibility with existing proof decoded from sized buffer
				StateVersion::V0
			} else {
				Decode::decode(input)?
			};
			Ok(StorageProof { trie_nodes, state_version })
		}
	}

	impl Decode for CompactProof {
		fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
			let encoded_nodes: Vec<Vec<u8>> = Decode::decode(input)?;
			let state_version = if let Ok(Some(0)) = input.remaining_len() {
				// for compatibility with existing proof decoded from sized buffer
				StateVersion::V0
			} else {
				Decode::decode(input)?
			};
			Ok(CompactProof { encoded_nodes, state_version })
		}
	}
}

impl StorageProof {
	/// Constructs a storage proof from a subset of encoded trie nodes in a storage backend.
	pub fn new(trie_nodes: Vec<Vec<u8>>, state_version: StateVersion) -> Self {
		StorageProof { trie_nodes, state_version }
	}

	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty() -> Self {
		StorageProof { trie_nodes: Vec::new(), state_version: StateVersion::default() }
	}

	/// Returns whether this is an empty proof.
	pub fn is_empty(&self) -> bool {
		self.trie_nodes.is_empty()
	}

	/// State version used in the proof.
	pub fn state_version(&self) -> StateVersion {
		self.state_version
	}

	/// Create an iterator over trie nodes constructed from the proof. The nodes are not guaranteed
	/// to be traversed in any particular order.
	pub fn iter_nodes(self) -> StorageProofNodeIterator {
		StorageProofNodeIterator::new(self)
	}

	/// Convert into plain node vector.
	pub fn into_nodes(self) -> Vec<Vec<u8>> {
		self.trie_nodes
	}
	/// Creates a `MemoryDB` from `Self`.
	pub fn into_memory_db<H: Hasher>(self) -> crate::MemoryDB<H> {
		self.into()
	}

	/// Creates a `MemoryDB` from `Self`. In case we do not need
	/// to check meta (using alt hashing will always be disabled).
	pub fn into_memory_db_no_meta<H: Hasher>(self) -> crate::MemoryDB<H> {
		let mut db = crate::MemoryDB::default();
		for item in self.iter_nodes() {
			db.insert(crate::EMPTY_PREFIX, &item);
		}
		db
	}

	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the
	/// input proofs due to deduplication of trie nodes.
	pub fn merge<I>(proofs: I) -> Self
	where
		I: IntoIterator<Item = Self>,
	{
		let mut state_version = StateVersion::default();
		let state_version = &mut state_version;
		let trie_nodes = proofs
			.into_iter()
			.flat_map(|proof| {
				debug_assert!(
					state_version == &StateVersion::default() ||
						state_version == &proof.state_version
				);
				*state_version = proof.state_version;
				proof.iter_nodes()
			})
			.collect::<sp_std::collections::btree_set::BTreeSet<_>>()
			.into_iter()
			.collect();

		Self { trie_nodes, state_version: *state_version }
	}

	/// Encode as a compact proof with default
	/// trie layout.
	pub fn into_compact_proof<H: Hasher>(
		self,
		root: H::Out,
	) -> Result<CompactProof, crate::CompactProofError<Layout<H>>> {
		crate::encode_compact::<Layout<H>>(self, root)
	}

	/// Returns the estimated encoded size of the compact proof.
	///
	/// Runing this operation is a slow operation (build the whole compact proof) and should only be
	/// in non sensitive path.
	/// Return `None` on error.
	pub fn encoded_compact_size<H: Hasher>(self, root: H::Out) -> Option<usize> {
		let compact_proof = self.into_compact_proof::<H>(root);
		compact_proof.ok().map(|p| p.encoded_size())
	}
}

impl CompactProof {
	/// Return an iterator on the compact encoded nodes.
	pub fn iter_compact_encoded_nodes(&self) -> impl Iterator<Item = &[u8]> {
		self.encoded_nodes.iter().map(Vec::as_slice)
	}

	/// Decode to a full storage_proof.
	///
	/// Method use a temporary `HashDB`, and `sp_trie::decode_compact`
	/// is often better.
	pub fn to_storage_proof<H: Hasher>(
		&self,
		expected_root: Option<&H::Out>,
	) -> Result<(StorageProof, H::Out), crate::CompactProofError<Layout<H>>> {
		let state_version = self.state_version;
		let mut db = crate::MemoryDB::<H>::new(&[]);
		let root = crate::decode_compact::<Layout<H>, _, _>(
			&mut db,
			self.iter_compact_encoded_nodes(),
			expected_root,
		)?;
		Ok((
			StorageProof::new(
				db.drain()
					.into_iter()
					.filter_map(|kv| if (kv.1).1 > 0 { Some((kv.1).0) } else { None })
					.collect(),
				state_version,
			),
			root,
		))
	}
}

/// An iterator over trie nodes constructed from a storage proof. The nodes are not guaranteed to
/// be traversed in any particular order.
pub struct StorageProofNodeIterator {
	inner: <Vec<Vec<u8>> as IntoIterator>::IntoIter,
}

impl StorageProofNodeIterator {
	fn new(proof: StorageProof) -> Self {
		StorageProofNodeIterator { inner: proof.trie_nodes.into_iter() }
	}
}

impl Iterator for StorageProofNodeIterator {
	type Item = Vec<u8>;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<H: Hasher> From<StorageProof> for crate::MemoryDB<H> {
	fn from(proof: StorageProof) -> Self {
		let mut db = crate::MemoryDB::default();
		for item in proof.trie_nodes.iter() {
			let mut meta = crate::Meta::default();
			meta.try_inner_hashing = match proof.state_version {
				StateVersion::V0 => None,
				StateVersion::V1 { threshold, .. } => Some(threshold),
			};
			// Read meta from state (required for value layout).
			let _ = <Layout<H> as TrieLayout>::Codec::decode_plan(item.as_slice(), &mut meta);
			db.alt_insert(
				crate::EMPTY_PREFIX,
				item,
				meta.resolve_alt_hashing::<<Layout<H> as TrieLayout>::Codec>(),
			);
		}
		db
	}
}
