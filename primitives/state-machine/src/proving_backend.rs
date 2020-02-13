// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Proving state machine backend.

use std::sync::Arc;
use parking_lot::RwLock;
use codec::{Decode, Encode, Codec};
use log::debug;
use hash_db::{HashDB, EMPTY_PREFIX, Prefix};
use sp_core::{Hasher, InnerHasher};
use sp_trie::{
	MemoryDB, default_child_trie_root, read_trie_value_with,
	record_all_keys,
};
pub use sp_trie::Recorder;
pub use sp_trie::trie_types::{Layout, TrieError};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{BackendStorageDBRef, TrieBackendEssence,
	TrieBackendStorage, TrieBackendStorageRef};
use crate::{Error, ExecutionError, Backend};
use std::collections::{HashMap, HashSet};
use crate::DBValue;
use sp_core::storage::{ChildInfo, ChildType, ChildrenMap};

/// Patricia trie-based backend specialized in get value proofs.
pub struct ProvingBackendRecorder<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	pub(crate) backend: &'a TrieBackendEssence<S, H>,
	pub(crate) proof_recorder: &'a mut Recorder<H::Out>,
}

#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StorageProofKind {
	/// The proof can be build by multiple child trie only if
	/// they are of the same kind, that way we can store all
	/// encoded node in the same container.
	Flatten,
/*	/// Top trie proof only, in compact form.
	TopTrieCompact,*/
	/// Proofs split by child trie.
	Full,
	/// Compact form of proofs split by child trie.
	FullCompact,
}

impl StorageProofKind {
	fn is_flatten(&self) -> bool {
		match self {
			StorageProofKind::Flatten => true,
			StorageProofKind::Full | StorageProofKind::FullCompact =>  false
		}
	}

	fn is_compact(&self) -> bool {
		match self {
			StorageProofKind::FullCompact => true,
			StorageProofKind::Full | StorageProofKind::Flatten =>  false
		}
	}
}

/// The possible compactions for proofs.
#[repr(u32)]
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub enum CompactScheme {
	/// This skip encoding of hashes that are
	/// calculated when reading the structue
	/// of the trie.
	TrieSkipHashes = 1,
}

type ProofNodes = Vec<Vec<u8>>;
type ProofCompacted = (CompactScheme, Vec<Vec<u8>>);

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// For default trie, the proof component consists of the set of serialized nodes in the storage trie
/// accessed when looking up the keys covered by the proof. Verifying the proof requires constructing
/// the partial trie from the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub enum StorageProof {
	/// Single flattened proof component, all default child trie are flattened over a same
	/// container, no child trie information is provided, this works only for proof accessing
	/// the same kind of child trie.
	Flatten(ProofNodes),
/*	/// If proof only cover a single trie, we compact the proof by ommitting some content
	/// that can be rebuild on construction. For patricia merkle trie it will be hashes that
	/// are not necessary between node, with indexing of the missing hash based on orders
	/// of nodes.
	TopTrieCompact(ProofCompacted),*/
	///	Fully descriped proof, it includes the child trie individual descriptions.
	Full(ChildrenMap<ProofNodes>),
	///	Fully descriped proof, compact encoded.
	FullCompact(ChildrenMap<ProofCompacted>),
}

impl StorageProof {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty(kind: StorageProofKind) -> Self {
		match kind {
			StorageProofKind::Flatten => StorageProof::Flatten(Default::default()),
			StorageProofKind::Full => StorageProof::Full(ChildrenMap::default()),
			StorageProofKind::FullCompact => StorageProof::FullCompact(ChildrenMap::default()),
		}
	}

	/// Returns whether this is an empty proof.
	pub fn is_empty(&self) -> bool {
		match self {
			StorageProof::Flatten(data) => data.is_empty(),
			StorageProof::Full(data) => data.is_empty(),
			StorageProof::FullCompact(data) => data.is_empty(),
		}
	}

	/// Create an iterator over trie nodes constructed from the proof. The nodes are not guaranteed
	/// to be traversed in any particular order.
	/// This iterator is only for `Flatten` proofs, other kind of proof will return an iterator with
	/// no content.
	pub fn iter_nodes_flatten(self) -> StorageProofNodeIterator {
		StorageProofNodeIterator::new(self)
	}

	/// This unpacks `FullCompact` to `Full` or do nothing.
	pub fn unpack<H: Hasher>(self, with_roots: bool) -> Result<(Self, Option<ChildrenMap<Vec<u8>>>), String> 
		where H::Out: Codec,
	{
		let map_e = |e| format!("Trie unpack error: {}", e);
		if let StorageProof::FullCompact(children) = self {
			let result = ChildrenMap::default();
			let roots = if with_roots {
				Some(ChildrenMap::default())
			} else {
				None
			};
			for (child_info, (compact_scheme, proof)) in children {
				match child_info.child_type() {
					ChildType::CryptoUniqueId => {
						match compact_scheme {
							CompactScheme::TrieSkipHashes => {
								// Note that we could check the proof from the unpacking.
								let (root, unpacked_proof) = sp_trie::unpack_proof::<Layout<H>>(proof.as_slice())
									.map_err(map_e)?;
								roots.as_mut().map(|roots| roots.insert(child_info.clone(), root.encode()));
								result.insert(child_info, unpacked_proof);
							},
						}
					}
				}
			}
			Ok((StorageProof::Full(result), roots))
		} else {
			Ok((self, None))
		}
	}

	/// This packs `Full` to `FullCompact`, using needed roots.
	pub fn pack<H: Hasher>(self, roots: ChildrenMap<Vec<u8>>) -> Result<Self, String> 
		where H::Out: Codec,
	{
		let map_e = |e| format!("Trie pack error: {}", e);
	
		if let StorageProof::Full(children) = self {
			let result = ChildrenMap::default();
			for (child_info, proof) in children {
				match child_info.child_type() {
					ChildType::CryptoUniqueId => {
						let root = roots.get(&child_info)
							.and_then(|r| Decode::decode(&mut &r[..]).ok())
							.ok_or_else(|| "Missing root for packing".to_string())?;
						let trie_nodes = sp_trie::pack_proof::<Layout<H>>(&root, &proof[..]).map_err(map_e)?;
						result.insert(child_info.clone(), (CompactScheme::TrieSkipHashes, trie_nodes));
					}
				}
			}
			Ok(StorageProof::FullCompact(result))
		} else {
			Ok(self)
		}
	}

	/// This flatten `Full` to `Flatten`.
	/// Note that if for some reason child proof were not
	/// attached to the top trie, they will be lost.
	/// Generally usage of Flatten kind or this function
	/// when using child trie is not recommended.
	pub fn flatten(self) -> Self {
		if let StorageProof::Full(children) = self {
			let mut result = Vec::new();
			children.into_iter().for_each(|(child_info, proof)| {
				match child_info.child_type() {
					ChildType::CryptoUniqueId => {
						// this can get merged with top, since it is proof we do not use prefix
						result.extend(proof);
					}
				}
			});
			StorageProof::Flatten(result)
		} else {
			self
		}
	}
}

/// An iterator over trie nodes constructed from a storage proof. The nodes are not guaranteed to
/// be traversed in any particular order.
pub struct StorageProofNodeIterator {
	inner: <Vec<Vec<u8>> as IntoIterator>::IntoIter,
}

impl StorageProofNodeIterator {
	fn new(proof: StorageProof) -> Self {
		match proof {
			StorageProof::Flatten(data) => StorageProofNodeIterator {
				inner: data.into_iter(),
			},
			_ => StorageProofNodeIterator {
				inner: Vec::new().into_iter(),
			},
		}
	}
}

impl Iterator for StorageProofNodeIterator {
	type Item = Vec<u8>;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

/// Merges multiple storage proofs covering potentially different sets of keys into one proof
/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
/// proofs due to deduplication of trie nodes.
/// Merge to `Flatten` if any item is flatten (we cannot unflatten), if not `Flatten` we output to
/// non compact form.
pub fn merge_storage_proofs<H, I>(proofs: I) -> Result<StorageProof, String>
	where
		I: IntoIterator<Item=StorageProof>,
		H: Hasher,
		H::Out: Codec,
{
	let mut final_proof = StorageProof::empty(StorageProofKind::Full);
	let child_sets = ChildrenMap::<HashSet<Vec<u8>>>::default();
	let unique_set = HashSet::<Vec<u8>>::default(); 
	let do_flatten = false;
	// lookup for best encoding
	for mut proof in proofs {
		if let &StorageProof::FullCompact(..) = &proof {
			proof = proof.unpack::<H>(false)?.0;
		}
		let proof = proof;
		match proof {
			StorageProof::Flatten(proof) => {
				if !do_flatten {
					do_flatten = true;
					for (_, set) in std::mem::replace(&mut child_sets, Default::default()).into_iter() {
						unique_set.extend(set);
					}
				}
			},
			StorageProof::Full(children) => {
				for (child_info, child) in children.into_iter() {
					if do_flatten {
						unique_set.extend(child);
					} else {
						let set = child_sets.entry(child_info).or_default();
						set.extend(child);
					}
				}
			},
			StorageProof::FullCompact(children) => unreachable!("unpacked when entering function"),
		}
	}
	Ok(if do_flatten {
		StorageProof::Flatten(unique_set.into_iter().collect())
	} else {
		let mut result = ChildrenMap::default();
		for (child_info, set) in child_sets.into_iter() {
			result.insert(child_info, set.into_iter().collect());
		}
		StorageProof::Full(result)
	})
}

/// Merge over flatten proof, return `None` if one of the proofs is not
/// a flatten proof.
pub fn merge_flatten_storage_proofs<I>(proofs: I) -> Option<StorageProof>
	where
		I: IntoIterator<Item=StorageProof>,
{
	let mut final_proof = StorageProof::empty(StorageProofKind::Full);
	let unique_set = HashSet::<Vec<u8>>::default(); 
	// lookup for best encoding
	for mut proof in proofs {
		if let StorageProof::Flatten(set) = proof {
			unique_set.extend(set);
		} else {
			return None;
		}
	}
	Some(StorageProof::Flatten(unique_set.into_iter().collect()))
}

impl<'a, S, H> ProvingBackendRecorder<'a, S, H>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Codec,
{
	/// Produce proof for a key query.
	pub fn storage(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let child_info = ChildInfo::top_trie();
		let eph = BackendStorageDBRef::new(
			self.backend.backend_storage(),
			&child_info,
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value_with::<Layout<H>, _, BackendStorageDBRef<S, H>>(
			&eph,
			self.backend.root(),
			key,
			&mut *self.proof_recorder,
		).map_err(map_e)
	}

	/// Produce proof for a child key query.
	pub fn child_storage(
		&mut self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, String> {
		let root = self.storage(storage_key)?
			.and_then(|r| Decode::decode(&mut &r[..]).ok())
			.unwrap_or(default_child_trie_root::<Layout<H>>(storage_key));

		let eph = BackendStorageDBRef::new(
			self.backend.backend_storage(),
			child_info,
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value_with::<Layout<H>, _, _>(
			&eph,
			&root,
			key,
			&mut *self.proof_recorder
		).map_err(map_e)
	}

	/// Produce proof for the whole backend.
	pub fn record_all_top_trie_keys(&mut self) {
		let child_info = ChildInfo::top_trie();
		let eph = BackendStorageDBRef::new(
			self.backend.backend_storage(),
			&child_info,
		);

		let mut iter = move || -> Result<(), Box<TrieError<H::Out>>> {
			let root = self.backend.root();
			record_all_keys::<Layout<H>, _>(&eph, root, &mut *self.proof_recorder)
		};

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while recording all keys: {}", e);
		}
	}
}

/// Global proof recorder, act as a layer over a hash db for recording queried
/// data.
pub enum ProofRecorder<H: InnerHasher> {
	// root of each child is added to be able to pack.
	Full(Arc<RwLock<ChildrenMap<HashMap<<H as InnerHasher>::Out, Option<DBValue>>>>>),
	Flat(Arc<RwLock<HashMap<<H as InnerHasher>::Out, Option<DBValue>>>>),
}

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> (
	TrieBackend<ProofRecorderBackend<'a, S, H>, H>,
);

/// Trie backend storage with its proof recorder.
pub struct ProofRecorderBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a S,
	proof_recorder: ProofRecorder<H>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H>
	where H::Out: Codec
{
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>, flatten: bool) -> Self {
		let proof_recorder = if flatten {
			ProofRecorder::Flat(Default::default())
		} else {
			ProofRecorder::Full(Default::default())
		};
		Self::new_with_recorder(backend, proof_recorder)
	}

	/// Create new proving backend with the given recorder.
	pub fn new_with_recorder(
		backend: &'a TrieBackend<S, H>,
		proof_recorder: ProofRecorder<H>,
	) -> Self {
		let essence = backend.essence();
		let root = essence.root().clone();
		let recorder = ProofRecorderBackend {
			backend: essence.backend_storage(),
			proof_recorder: proof_recorder,
		};
		ProvingBackend(TrieBackend::new(recorder, root))
	}

	/// Extracting the gathered unordered proof.
	pub fn extract_proof(&self) -> Result<StorageProof, String> {
		Ok(match self.0.essence().backend_storage().proof_recorder {
			ProofRecorder::Flat(rec) => {
				let trie_nodes = rec
					.read()
					.iter()
					.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
					.collect();
				StorageProof::Flatten(trie_nodes)
			},
			ProofRecorder::Full(rec) => {
				let mut children = ChildrenMap::default();
				for (child_info, set) in rec.read().iter() {
					let trie_nodes: Vec<Vec<u8>> = set
						.iter()
						.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
						.collect();
					children.insert(child_info.clone(), trie_nodes);
				}
				StorageProof::Full(children)
			},
		})
	}
}

// proof run on a flatten storage of tries and currently only need implement a single
// trie backend storage api.
impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> TrieBackendStorageRef<H>
	for ProofRecorderBackend<'a, S, H>
{
	type Overlay = S::Overlay;

	fn get(
		&self,
		child_info: &ChildInfo,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String> {
		match self.proof_recorder {
			ProofRecorder::Flat(rec) => {
				if let Some(v) = rec.read().get(key) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.write().insert(key.clone(), backend_value.clone());
				Ok(backend_value)
			},
			ProofRecorder::Full(rec) => {
				if let Some(v) = rec.read().get(child_info).and_then(|s| s.get(key)) {
					return Ok(v.clone());
				}
				let backend_value = self.backend.get(child_info, key, prefix)?;
				rec.write().entry(child_info.clone())
					.or_default()
					.insert(key.clone(), backend_value.clone());
				Ok(backend_value)
			},
		}
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> std::fmt::Debug
	for ProvingBackend<'a, S, H>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ProvingBackend")
	}
}

impl<'a, S, H> Backend<H> for ProvingBackend<'a, S, H>
	where
		S: 'a + TrieBackendStorage<H>,
		H: 'a + Hasher,
		H::Out: Ord + Codec,
{
	type Error = String;
	type Transaction = Option<S::Overlay>;
	type TrieBackendStorage = S;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.storage(key)
	}

	fn child_storage(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.child_storage(storage_key, child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		f: F,
	) {
		self.0.for_keys_in_child_storage(storage_key, child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_child_storage_key(storage_key, child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.0.for_child_keys_with_prefix(storage_key, child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.0.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.0.keys(prefix)
	}

	fn child_keys(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.0.child_keys(storage_key, child_info, prefix)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let (root, mut tx) = self.0.storage_root(delta);
		(root, tx.remove(&ChildInfo::top_trie()))
	}

	fn child_storage_root<I>(
		&self,
		storage_key: &[u8],
		child_info: &ChildInfo,
		delta: I,
	) -> (H::Out, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		let (root, is_empty, mut tx) = self.0.child_storage_root(storage_key, child_info, delta);
		(root, is_empty, tx.remove(child_info))
	}
}

/// Create flat proof check backend.
pub fn create_flat_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<MemoryDB<H>, H>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	let db = create_flat_proof_check_backend_storage(proof);

	if db.contains(&root, EMPTY_PREFIX) {
		Ok(TrieBackend::new(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

/// Create proof check backend.
pub fn create_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<ChildrenMap<MemoryDB<H>>, H>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	use std::ops::Deref;
	if let Ok(db) = create_proof_check_backend_storage(proof) {
		if db.deref().get(&ChildInfo::top_trie())
			.map(|db| db.contains(&root, EMPTY_PREFIX))
			.unwrap_or(false) {
			return Ok(TrieBackend::new(db, root))
		}
	}
	return	Err(Box::new(ExecutionError::InvalidProof));
}

/// Create in-memory storage of proof check backend.
pub fn create_proof_check_backend_storage<H>(
	proof: StorageProof,
) -> Result<ChildrenMap<MemoryDB<H>>, String>
where
	H: Hasher,
{
	let map_e = |e| format!("Trie unpack error: {}", e);
	let mut result = ChildrenMap::default();
	match proof {
		f@StorageProof::Flatten(..) => {
			let db = create_flat_proof_check_backend_storage(f);
			result.insert(ChildInfo::top_trie(), db);
		},
		StorageProof::Full(children) => {
			for (child_info, proof) in children.into_iter() {
				let mut db = MemoryDB::default();
				for item in proof.into_iter() {
					db.insert(EMPTY_PREFIX, &item);
				}
				result.insert(child_info, db);
			}
		},
		StorageProof::FullCompact(children) => {
			for (child_info, (compact_scheme, proof)) in children.into_iter() {
				match compact_scheme {
					CompactScheme::TrieSkipHashes => {
						// Note that this does check all hashes so using a trie backend
						// for further check is not really good (could use a direct value backend).
						let (_root, db) = sp_trie::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())
								.map_err(map_e)?;
						result.insert(child_info, db);
					},
				}
			}
		},
	}
	Ok(result)
}


/// Create in-memory storage of proof check backend.
pub fn create_flat_proof_check_backend_storage<H>(
	proof: StorageProof,
) -> MemoryDB<H>
where
	H: Hasher,
{
	let mut db = MemoryDB::default();
	for item in proof.iter_nodes_flatten() {
		db.insert(EMPTY_PREFIX, &item);
	}
	db
}

#[cfg(test)]
mod tests {
	use crate::InMemoryBackend;
	use crate::trie_backend::tests::test_trie;
	use super::*;
	use sp_core::{Blake2Hasher, storage::ChildStorageKey};
	use crate::proving_backend::create_proof_check_backend;
	use sp_trie::PrefixedMemoryDB;

	fn test_proving<'a>(
		trie_backend: &'a TrieBackend<PrefixedMemoryDB<Blake2Hasher>,Blake2Hasher>,
	) -> ProvingBackend<'a, PrefixedMemoryDB<Blake2Hasher>, Blake2Hasher> {
		ProvingBackend::new(trie_backend)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		let trie_backend = test_trie();
		assert!(test_proving(&trie_backend).extract_proof().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		let trie_backend = test_trie();
		let backend = test_proving(&trie_backend);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		use sp_core::H256;
		let result = create_proof_check_backend::<Blake2Hasher>(
			H256::from_low_u64_be(1),
			StorageProof::empty()
		);
		assert!(result.is_err());
	}

	#[test]
	fn passes_throgh_backend_calls() {
		let trie_backend = test_trie();
		let proving_backend = test_proving(&trie_backend);
		assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
		assert_eq!(trie_backend.pairs(), proving_backend.pairs());

		let (trie_root, mut trie_mdb) = trie_backend.storage_root(::std::iter::empty());
		let (proving_root, proving_mdb) = proving_backend.storage_root(::std::iter::empty());
		assert_eq!(trie_root, proving_root);
		let mut trie_mdb = trie_mdb.remove(&ChildInfo::top_trie()).unwrap();
		assert_eq!(trie_mdb.drain(), proving_mdb.unwrap().drain());
	}

	#[test]
	fn proof_recorded_and_checked() {
		let contents = (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemoryBackend::<Blake2Hasher>::default();
		let mut in_memory = in_memory.update(vec![(None, contents)]);
		let in_memory_root = in_memory.storage_root(::std::iter::empty()).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check = create_proof_check_backend::<Blake2Hasher>(in_memory_root.into(), proof).unwrap();
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
	}

	#[test]
	fn proof_recorded_and_checked_with_child() {
		let child_info1 = ChildInfo::new_default(b"unique_id_1");
		let child_info2 = ChildInfo::new_default(b"unique_id_2");
		let subtrie1 = ChildStorageKey::from_slice(b":child_storage:default:sub1").unwrap();
		let subtrie2 = ChildStorageKey::from_slice(b":child_storage:default:sub2").unwrap();
		let own1 = subtrie1.into_owned();
		let own2 = subtrie2.into_owned();
		let contents = vec![
			(None, (0..64).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some((own1.clone(), child_info1.clone())),
				(28..65).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some((own2.clone(), child_info2.clone())),
				(10..15).map(|i| (vec![i], Some(vec![i]))).collect()),
		];
		let in_memory = InMemoryBackend::<Blake2Hasher>::default();
		let mut in_memory = in_memory.update(contents);
		let in_memory_root = in_memory.full_storage_root::<_, Vec<_>, _>(
			::std::iter::empty(),
			in_memory.child_storage_keys().map(|k|(k.0.to_vec(), Vec::new(), k.1.to_owned())),
			false,
		).0;
		(0..64).for_each(|i| assert_eq!(
			in_memory.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));
		(28..65).for_each(|i| assert_eq!(
			in_memory.child_storage(&own1[..], &child_info1, &[i]).unwrap().unwrap(),
			vec![i]
		));
		(10..15).for_each(|i| assert_eq!(
			in_memory.child_storage(&own2[..], &child_info2, &[i]).unwrap().unwrap(),
			vec![i]
		));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(
			trie.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check = create_proof_check_backend::<Blake2Hasher>(
			in_memory_root.into(),
			proof
		).unwrap();
		assert!(proof_check.storage(&[0]).is_err());
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		// note that it is include in root because proof close
		assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
		assert_eq!(proof_check.storage(&[64]).unwrap(), None);

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.child_storage(&own1[..], &child_info1, &[64]), Ok(Some(vec![64])));

		let proof = proving.extract_proof();
		let proof_check = create_proof_check_backend::<Blake2Hasher>(
			in_memory_root.into(),
			proof
		).unwrap();
		assert_eq!(
			proof_check.child_storage(&own1[..], &child_info1, &[64]).unwrap().unwrap(),
			vec![64]
		);
	}
}
