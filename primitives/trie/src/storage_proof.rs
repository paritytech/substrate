// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use sp_std::collections::btree_map::BTreeMap;
use sp_std::collections::btree_set::BTreeSet;
use sp_std::vec::Vec;
use codec::{Codec, Encode, Decode};
use hash_db::{Hasher, HashDB, EMPTY_PREFIX};
use crate::{MemoryDB, Layout};
use sp_storage::{ChildInfoProof, ChildType};
use crate::TrieError;

type Result<T, H> = sp_std::result::Result<T, sp_std::boxed::Box<TrieError<Layout<H>>>>;

fn missing_pack_input<H: Hasher>() -> sp_std::boxed::Box<TrieError<Layout<H>>> {
	// TODO better error in trie db crate eg Packing error
	sp_std::boxed::Box::new(TrieError::<Layout<H>>::IncompleteDatabase(Default::default()))
}

/// Different kind of proof representation are allowed.
/// This definition is used as input parameter when producing
/// a storage proof.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum StorageProofKind {
	/// The proof can be build by multiple child trie only when
	/// their query can be done on a single memory backend,
	/// all encoded node can be stored in the same container.
	Flatten,
	// FlattenCompact(CompactScheme),
	/// Proofs split by child trie.
	Full,
	/// Compact form of proofs split by child trie.
	/// TODO indicate compact scheme to use (BtreeMap?)
	FullCompact,
}

impl StorageProofKind {
	/// Is proof stored in a unique structure or
	/// different structure depending on child trie.
	pub fn is_flatten(&self) -> bool {
		match self {
			StorageProofKind::Flatten => true,
			StorageProofKind::Full | StorageProofKind::FullCompact => false,
		}
	}

	/// Is the proof compacted. Compaction requires
	/// using state root of every child trie.
	pub fn is_compact(&self) -> bool {
		match self {
			StorageProofKind::FullCompact => true,
			StorageProofKind::Full | StorageProofKind::Flatten => false,
		}
	}

	/// Indicate if we need all child trie information
	/// to get register for producing the proof.
	pub fn need_register_full(&self) -> bool {
		match self {
			StorageProofKind::Flatten => false,
	//		StorageProofKind::FlattenCompact => true,
			StorageProofKind::Full | StorageProofKind::FullCompact => true,
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
/*	/// Skip encoding of hashes and values,
	/// we need to know them when when unpacking.
	KnownQueryPlanAndValues = 2,
	/// Skip encoding of hashes, this need knowing
	/// the queried keys when unpacking, can be faster
	/// than `TrieSkipHashes` but with similar packing
	/// gain.
	KnownQueryPlan = 3,*/
}

type ProofNodes = Vec<Vec<u8>>;
// TODO EMCH do not alloc scheme per child for now
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
/* TODO EMCH implement as it will be default for trie skip hashes	/// Proof can address multiple child trie, but results in a single flatten
	/// db backend.
	FlattenCompact(Vec<ProofCompacted>),*/
	///	Fully descriBed proof, it includes the child trie individual descriptions.
	///	Currently Full variant are not of any use as we have only child trie that can use the same
	///	memory db backend.
	///	TODO EMCH consider removal: could be put back when needed, and probably
	///	with a new StorageProof key that is the same for a flattenable kind.
	Full(ChildrenProofMap<ProofNodes>),
	///	Fully descriped proof, compact encoded.
	FullCompact(ChildrenProofMap<ProofCompacted>),
}

impl StorageProof {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty() -> Self {
		// we default to full as it can be reduce to flatten when reducing
		// flatten to full is not possible without making asumption over the content.
		Self::empty_for(StorageProofKind::Full)
	}

	/// Returns a new empty proof of a given kind.
	pub fn empty_for(kind: StorageProofKind) -> Self {
		match kind {
			StorageProofKind::Flatten => StorageProof::Flatten(Default::default()),
			StorageProofKind::Full => StorageProof::Full(ChildrenProofMap::default()),
			StorageProofKind::FullCompact => StorageProof::FullCompact(ChildrenProofMap::default()),
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
	/// TODO EMCH document and use case for with_roots to true?? (probably unpack -> merge -> pack
	/// but no code for it here)
	pub fn unpack<H: Hasher>(
		self,
		with_roots: bool,
	) -> Result<(Self, Option<ChildrenProofMap<Vec<u8>>>), H>
		where H::Out: Codec,
	{
		if let StorageProof::FullCompact(children) = self {
			let mut result = ChildrenProofMap::default();
			let mut roots = if with_roots {
				Some(ChildrenProofMap::default())
			} else {
				None
			};
			for (child_info, (compact_scheme, proof)) in children {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
						match compact_scheme {
							CompactScheme::TrieSkipHashes => {
								// Note that we could check the proof from the unpacking.
								let (root, unpacked_proof) = crate::unpack_proof::<Layout<H>>(proof.as_slice())?;
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
	pub fn pack<H: Hasher>(
		self,
		roots: &ChildrenProofMap<Vec<u8>>,
	) -> Result<Self, H>
		where H::Out: Codec,
	{
		if let StorageProof::Full(children) = self {
			let mut result = ChildrenProofMap::default();
			for (child_info, proof) in children {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
						let root = roots.get(&child_info)
							.and_then(|r| Decode::decode(&mut &r[..]).ok())
							.ok_or_else(|| missing_pack_input::<H>())?;
						// TODO EMCH pack directly from memory db, here we switch 
						let trie_nodes = crate::pack_proof::<Layout<H>>(&root, &proof[..])?;
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
	pub fn flatten(self) -> Self {
		if let StorageProof::Full(children) = self {
			let mut result = Vec::new();
			children.into_iter().for_each(|(child_info, proof)| {
				match child_info.child_type() {
					ChildType::ParentKeyId => {
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

	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	/// Merge to `Flatten` if one of the item is flatten (we cannot unflatten), if not `Flatten` we output to
	/// non compact form.
	pub fn merge<H, I>(proofs: I) -> Result<StorageProof, H>
		where
			I: IntoIterator<Item=StorageProof>,
			H: Hasher,
			H::Out: Codec,
	{
		let mut do_flatten = false;
		let mut child_sets = ChildrenProofMap::<BTreeSet<Vec<u8>>>::default();
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		// lookup for best encoding
		for mut proof in proofs {
			if let &StorageProof::FullCompact(..) = &proof {
				// TODO EMCH pack back so set to true.
				proof = proof.unpack::<H>(false)?.0;
			}
			let proof = proof;
			match proof {
				StorageProof::Flatten(proof) => {
					if !do_flatten {
						do_flatten = true;
						for (_, set) in sp_std::mem::replace(&mut child_sets, Default::default()).into_iter() {
							unique_set.extend(set);
						}
					}
					unique_set.extend(proof);
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
				StorageProof::FullCompact(_children) => unreachable!("unpacked when entering function"),
			}
		}
		Ok(if do_flatten {
			StorageProof::Flatten(unique_set.into_iter().collect())
		} else {
			let mut result = ChildrenProofMap::default();
			for (child_info, set) in child_sets.into_iter() {
				result.insert(child_info, set.into_iter().collect());
			}
			StorageProof::Full(result)
		})
	}

	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	///
	/// Run only over flatten proof, will return `None` if one of the proofs is not
	/// a flatten proof.
	pub fn merge_flat<I>(proofs: I) -> Option<StorageProof>
		where
			I: IntoIterator<Item=StorageProof>,
	{
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		// lookup for best encoding
		for proof in proofs {
			if let StorageProof::Flatten(set) = proof {
				unique_set.extend(set);
			} else {
				return None;
			}
		}
		Some(StorageProof::Flatten(unique_set.into_iter().collect()))
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

// TODO EMCH use tryfrom instead of those two create.

/// Create in-memory storage of proof check backend.
/// Currently child trie are all with same backend
/// implementation, therefore using
/// `create_flat_proof_check_backend_storage` is prefered.
/// TODO flat proof check is enough for now, do we want to
/// maintain the full variant?
pub fn create_proof_check_backend_storage<H>(
	proof: StorageProof,
) -> Result<ChildrenProofMap<MemoryDB<H>>, H>
where
	H: Hasher,
{
	let mut result = ChildrenProofMap::default();
	match proof {
		s@StorageProof::Flatten(..) => {
			let mut db = MemoryDB::default();
			for item in s.iter_nodes_flatten() {
				db.insert(EMPTY_PREFIX, &item);
			}
			result.insert(ChildInfoProof::top_trie(), db);
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
						let (_root, db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
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
) -> Result<MemoryDB<H>, H>
where
	H: Hasher,
{
	let mut db = MemoryDB::default();
	match proof {
		s@StorageProof::Flatten(..) => {
			for item in s.iter_nodes_flatten() {
				db.insert(EMPTY_PREFIX, &item);
			}
		},
		StorageProof::Full(children) => {
			for (_child_info, proof) in children.into_iter() {
				for item in proof.into_iter() {
					db.insert(EMPTY_PREFIX, &item);
				}
			}
		},
		StorageProof::FullCompact(children) => {
			for (_child_info, (compact_scheme, proof)) in children.into_iter() {
				match compact_scheme {
					CompactScheme::TrieSkipHashes => {
						// Note that this does check all hashes so using a trie backend
						// for further check is not really good (could use a direct value backend).
						let (_root, child_db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
						db.consolidate(child_db);
					},
				}
			}
		},
	}
	Ok(db)
}

#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
/// Type for storing a map of child trie proof related information.
/// A few utilities methods are defined.
pub struct ChildrenProofMap<T>(pub BTreeMap<ChildInfoProof, T>);

impl<T> sp_std::ops::Deref for ChildrenProofMap<T> {
	type Target = BTreeMap<ChildInfoProof, T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T> sp_std::ops::DerefMut for ChildrenProofMap<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<T> sp_std::default::Default for ChildrenProofMap<T> {
	fn default() -> Self {
		ChildrenProofMap(BTreeMap::new())
	}
}

impl<T> IntoIterator for ChildrenProofMap<T> {
	type Item = (ChildInfoProof, T);
	type IntoIter = sp_std::collections::btree_map::IntoIter<ChildInfoProof, T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}
