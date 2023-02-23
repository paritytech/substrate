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

use codec::{Decode, Encode};
use hash_db::{HashDB, Hasher};
use scale_info::TypeInfo;
use sp_std::{
	collections::btree_set::BTreeSet,
	iter::{DoubleEndedIterator, IntoIterator},
	vec::Vec,
};
// Note that `LayoutV1` usage here (proof compaction) is compatible
// with `LayoutV0`.
use crate::LayoutV1 as Layout;

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// The proof consists of the set of serialized nodes in the storage trie accessed when looking up
/// the keys covered by the proof. Verifying the proof requires constructing the partial trie from
/// the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode, TypeInfo)]
pub struct StorageProof {
	trie_nodes: BTreeSet<Vec<u8>>,
}

impl StorageProof {
	/// Constructs a storage proof from a subset of encoded trie nodes in a storage backend.
	pub fn new(trie_nodes: impl IntoIterator<Item = Vec<u8>>) -> Self {
		StorageProof { trie_nodes: BTreeSet::from_iter(trie_nodes) }
	}

	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty() -> Self {
		StorageProof { trie_nodes: BTreeSet::new() }
	}

	/// Returns whether this is an empty proof.
	pub fn is_empty(&self) -> bool {
		self.trie_nodes.is_empty()
	}

	/// Convert into an iterator over encoded trie nodes in lexicographical order constructed
	/// from the proof.
	pub fn into_iter_nodes(self) -> impl Sized + DoubleEndedIterator<Item = Vec<u8>> {
		self.trie_nodes.into_iter()
	}

	/// Create an iterator over encoded trie nodes in lexicographical order constructed
	/// from the proof.
	pub fn iter_nodes(&self) -> impl Sized + DoubleEndedIterator<Item = &Vec<u8>> {
		self.trie_nodes.iter()
	}

	/// Convert into plain node vector.
	pub fn into_nodes(self) -> BTreeSet<Vec<u8>> {
		self.trie_nodes
	}

	/// Creates a [`MemoryDB`](crate::MemoryDB) from `Self`.
	pub fn into_memory_db<H: Hasher>(self) -> crate::MemoryDB<H> {
		self.into()
	}

	/// Creates a [`MemoryDB`](crate::MemoryDB) from `Self` reference.
	pub fn to_memory_db<H: Hasher>(&self) -> crate::MemoryDB<H> {
		self.into()
	}

	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the
	/// input proofs due to deduplication of trie nodes.
	pub fn merge(proofs: impl IntoIterator<Item = Self>) -> Self {
		let trie_nodes = proofs
			.into_iter()
			.flat_map(|proof| proof.into_iter_nodes())
			.collect::<BTreeSet<_>>()
			.into_iter()
			.collect();

		Self { trie_nodes }
	}

	/// Encode as a compact proof with default trie layout.
	pub fn into_compact_proof<H: Hasher>(
		self,
		root: H::Out,
	) -> Result<CompactProof, crate::CompactProofError<H::Out, crate::Error<H::Out>>> {
		let db = self.into_memory_db();
		crate::encode_compact::<Layout<H>, crate::MemoryDB<H>>(&db, &root)
	}

	/// Encode as a compact proof with default trie layout.
	pub fn to_compact_proof<H: Hasher>(
		&self,
		root: H::Out,
	) -> Result<CompactProof, crate::CompactProofError<H::Out, crate::Error<H::Out>>> {
		let db = self.to_memory_db();
		crate::encode_compact::<Layout<H>, crate::MemoryDB<H>>(&db, &root)
	}

	/// Returns the estimated encoded size of the compact proof.
	///
	/// Running this operation is a slow operation (build the whole compact proof) and should only
	/// be in non sensitive path.
	///
	/// Return `None` on error.
	pub fn encoded_compact_size<H: Hasher>(self, root: H::Out) -> Option<usize> {
		let compact_proof = self.into_compact_proof::<H>(root);
		compact_proof.ok().map(|p| p.encoded_size())
	}
}

impl<H: Hasher> From<StorageProof> for crate::MemoryDB<H> {
	fn from(proof: StorageProof) -> Self {
		From::from(&proof)
	}
}

impl<H: Hasher> From<&StorageProof> for crate::MemoryDB<H> {
	fn from(proof: &StorageProof) -> Self {
		let mut db = crate::MemoryDB::default();
		proof.iter_nodes().for_each(|n| {
			db.insert(crate::EMPTY_PREFIX, &n);
		});
		db
	}
}

/// Storage proof in compact form.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode, TypeInfo)]
pub struct CompactProof {
	pub encoded_nodes: Vec<Vec<u8>>,
}

impl CompactProof {
	/// Return an iterator on the compact encoded nodes.
	pub fn iter_compact_encoded_nodes(&self) -> impl Iterator<Item = &[u8]> {
		self.encoded_nodes.iter().map(Vec::as_slice)
	}

	/// Decode to a full storage_proof.
	pub fn to_storage_proof<H: Hasher>(
		&self,
		expected_root: Option<&H::Out>,
	) -> Result<(StorageProof, H::Out), crate::CompactProofError<H::Out, crate::Error<H::Out>>> {
		let mut db = crate::MemoryDB::<H>::new(&[]);
		let root = crate::decode_compact::<Layout<H>, _, _>(
			&mut db,
			self.iter_compact_encoded_nodes(),
			expected_root,
		)?;
		Ok((
			StorageProof::new(db.drain().into_iter().filter_map(|kv| {
				if (kv.1).1 > 0 {
					Some((kv.1).0)
				} else {
					None
				}
			})),
			root,
		))
	}

	/// Convert self into a [`MemoryDB`](crate::MemoryDB).
	///
	/// `expected_root` is the expected root of this compact proof.
	///
	/// Returns the memory db and the root of the trie.
	pub fn to_memory_db<H: Hasher>(
		&self,
		expected_root: Option<&H::Out>,
	) -> Result<(crate::MemoryDB<H>, H::Out), crate::CompactProofError<H::Out, crate::Error<H::Out>>>
	{
		let mut db = crate::MemoryDB::<H>::new(&[]);
		let root = crate::decode_compact::<Layout<H>, _, _>(
			&mut db,
			self.iter_compact_encoded_nodes(),
			expected_root,
		)?;

		Ok((db, root))
	}
}
