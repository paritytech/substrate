// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Trie storage proofs that are a compacted collection of encoded nodes.

use super::*;
use super::simple::ProofNodes;
use codec::{Codec, Encode, Decode};
use crate::TrieLayout;
use crate::TrieHash;
use sp_storage::ChildType;
use sp_std::marker::PhantomData;
use sp_std::convert::TryInto;
use sp_std::{vec, vec::Vec};

/// A collection on encoded and compacted trie nodes.
/// Nodes are sorted by trie node iteration order, and some hash
/// and/or values are ommitted (they can be either calculated from
/// proof content or completed by proof input).
pub type ProofCompacted = Vec<Vec<u8>>;

/// Compacted flat proof.
///
/// This works as `Flat`, but skips encoding of hashes
/// that can be calculated when reading the child nodes
/// in the proof (nodes ordering hold the trie structure information).
/// This requires that the proof is collected with
/// child trie separation and each child trie roots as additional
/// input.
/// We remove child trie info when encoding because it is not strictly needed
/// when decoding.
#[derive(Encode, Decode)]
pub struct Flat<T>(Vec<ProofCompacted>, PhantomData<T>);

impl<T> PartialEq<Flat<T>> for Flat<T> {
	fn eq(&self, other: &Flat<T>) -> bool {
		self.0.eq(&other.0)
	}
}
impl<T> Eq for Flat<T> { }
	
impl<T> sp_std::fmt::Debug for Flat<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "Flat compact proof: {:?}", &self.0)
	}
}

impl<T> Clone for Flat<T> {
	fn clone(&self) -> Self {
		Flat(self.0.clone(), PhantomData)
	}
}

/// Compacted proof with child trie .
///
///	This currently mainly provided for test purpose and extensibility.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
pub struct Full<T>(ChildrenProofMap<ProofCompacted>, PhantomData<T>);

impl<T> sp_std::fmt::Debug for Full<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "Full compact proof: {:?}", &self.0)
	}
}

/// Proof cotaining an intermediate representation of state
/// which is mergeable and can be converted to compact representation.
/// Compatible with `TrieSkipHashes` and `TrieSkipHashesFull` proofs.
///
/// This is needed mainly for technical reasons (merge then compact proofs).
/// (though if possible user should rather use a flat record
/// backend in the different context and avoid merge).
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct FullForMerge(ChildrenProofMap<(ProofMapTrieNodes, Vec<u8>)>);

impl<T> Common for Flat<T> {
	fn empty() -> Self {
		Flat(Default::default(), PhantomData)
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

impl<T> Common for Full<T> {
	fn empty() -> Self {
		Full(Default::default(), PhantomData)
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

impl Common for FullForMerge {
	fn empty() -> Self {
		FullForMerge(Default::default())
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

/// Note that this implementation assumes all proof are from a same state.
impl Mergeable for FullForMerge {
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self> {
		// TODO EMCH optimize all merge to init to first element
		let mut child_sets = ChildrenProofMap::<(ProofMapTrieNodes, Vec<u8>)>::default();
		for children in proofs {
			for (child_info, (mut proof, root)) in children.0.into_iter() {
				child_sets.entry(child_info)
					.and_modify(|entry| {
						debug_assert!(&root == &entry.1);
						let iter_proof = sp_std::mem::replace(&mut proof, Default::default());
						entry.0.extend(iter_proof.0.into_iter());
					})
					.or_insert((proof, root));
			}
		}
		FullForMerge(child_sets)
	}
}

impl<T> Recordable<T::Hash> for Flat<T>
	where
		T: TrieLayout,
		TrieHash<T>: Decode,
{
	const INPUT_KIND: InputKind = InputKind::ChildTrieRoots;

	type RecordBackend = super::FullRecorder<T::Hash>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		if let Input::ChildTrieRoots(roots) = input {
			let mut result = Vec::default();
			for (child_info, set) in recorder.0.iter() {
				let root = roots.get(&child_info.proof_info())
					.and_then(|r| Decode::decode(&mut &r[..]).ok())
					.ok_or_else(|| missing_pack_input())?;
				let trie_nodes = crate::pack_proof_from_collected::<T>(&root, set)?;
				result.push(trie_nodes);
			}
			Ok(Flat(result, PhantomData))
		} else {
			Err(missing_pack_input())
		}
	}
}

impl<T> Recordable<T::Hash> for Full<T>
	where
		T: TrieLayout,
		TrieHash<T>: Decode,
{
	const INPUT_KIND: InputKind = InputKind::ChildTrieRoots;

	type RecordBackend = super::FullRecorder<T::Hash>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		if let Input::ChildTrieRoots(roots) = input {
			let mut result = ChildrenProofMap::default();
			for (child_info, set) in recorder.0.iter() {
				let root = roots.get(&child_info.proof_info())
					.and_then(|r| Decode::decode(&mut &r[..]).ok())
					.ok_or_else(|| missing_pack_input())?;
				let trie_nodes = crate::pack_proof_from_collected::<T>(&root, set)?;
				result.insert(child_info.proof_info(), trie_nodes);
			}
			Ok(Full(result, PhantomData))
		} else {
			Err(missing_pack_input())
		}
	}
}

impl<H> Recordable<H> for FullForMerge
	where
		H: Hasher,
		H::Out: Encode,
{
	const INPUT_KIND: InputKind = InputKind::ChildTrieRoots;

	type RecordBackend = super::FullRecorder<H>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		if let Input::ChildTrieRoots(roots) = input {
			let mut result = ChildrenProofMap::default();
			for (child_info, set) in recorder.0.iter() {
				let root = roots.get(&child_info.proof_info())
					.ok_or_else(|| missing_pack_input())?.clone();
				let trie_nodes: BTreeMap<_, _> = set
					.iter()
					.filter_map(|(k, v)| v.as_ref().map(|v| (k.encode(), v.to_vec())))
					.collect();
				result.insert(child_info.proof_info(), (ProofMapTrieNodes(trie_nodes), root));
			}
			Ok(FullForMerge(result))
		} else {
			Err(missing_pack_input())
		}
	}
}

impl<T> BackendProof<T::Hash> for Flat<T>
	where
		T: TrieLayout,
		TrieHash<T>: Codec,
{
	type ProofRaw = FullForMerge;

	fn into_partial_db(self) -> Result<MemoryDB<T::Hash>> {
		let mut db = MemoryDB::default();
		let mut db_empty = true;
		for proof in self.0.into_iter() {
			let (_root, child_db) = crate::unpack_proof_to_memdb::<T>(proof.as_slice())?;
			if db_empty {
				db_empty = false;
				db = child_db;
			} else {
				db.consolidate(child_db);
			}
		}
		Ok(db)
	}
}

impl<T> BackendProof<T::Hash> for Full<T>
	where
		T: TrieLayout,
		TrieHash<T>: Codec,
{
	type ProofRaw = FullForMerge;

	fn into_partial_db(self) -> Result<MemoryDB<T::Hash>> {
		let mut db = MemoryDB::default();
		let mut db_empty = true;
		for (_child_info, proof) in self.0.into_iter() {
			let (_root, child_db) = crate::unpack_proof_to_memdb::<T>(proof.as_slice())?;
			if db_empty {
				db_empty = false;
				db = child_db;
			} else {
				db.consolidate(child_db);
			}
		}
		Ok(db)
	}
}

impl<T> FullBackendProof<T::Hash> for Full<T>
	where
		T: TrieLayout,
		TrieHash<T>: Codec,
{
	fn into_partial_full_db(self) -> Result<ChildrenProofMap<MemoryDB<T::Hash>>> {
		let mut result = ChildrenProofMap::default();
		for (child_info, proof) in self.0 {
			// Note that this does check all hashes by using a trie backend
			let (_root, db) = crate::unpack_proof_to_memdb::<T>(proof.as_slice())?;
			result.insert(child_info, db);
		}
		Ok(result)
	}
}

// Note that this implementation is only possible
// as long as we only have default child trie which
// can be flattened into top trie storage.
impl<L> Into<Flat<L>> for Full<L> {
	fn into(self) -> Flat<L> {
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		for (child_info, nodes) in self.0 {
			assert!(matches!(child_info, ChildInfoProof::Default(..)));
			unique_set.extend(nodes);
		}
		Flat(vec![unique_set.into_iter().collect()], PhantomData)
	}
}

// TODO switch to try into (works only for one compact flat)
impl<L> Into<Full<L>> for Flat<L> {
	fn into(mut self) -> Full<L> {
		assert!(self.0.len() == 1); // works only if only top trie
		let mut result = ChildrenProofMap::default();
		result.insert(ChildInfoProof::top_trie(), self.0.pop().expect("asserted above; qed"));
		Full(result, PhantomData)
	}
}

impl FullForMerge {
	// TODO EMCH use try_into!
	fn to_full<L>(self) -> Result<Full<L>>
		where
			L: TrieLayout,
			TrieHash<L>: Codec,
	{
		let mut result = ChildrenProofMap::<ProofCompacted>::default();
		for (child_info, (set, root)) in self.0.into_iter() {
			let root = Decode::decode(&mut &root[..])
				.map_err(|_e| pack_error())?;
			let trie_nodes = crate::pack_proof_from_collected::<L>(&root, &set)
				.map_err(|_e| pack_error())?;
			result.insert(child_info, trie_nodes);
		}
		Ok(Full(result, PhantomData))
	}

	// TODO EMCH use try_into!
	fn to_flat<L>(self) -> Result<Flat<L>>
		where
			L: TrieLayout,
			TrieHash<L>: Codec,
	{
		let mut result = Vec::<ProofCompacted>::default();
		for (_child_info, (set, root)) in self.0.into_iter() {
			let root = Decode::decode(&mut &root[..])
				.map_err(|_e| pack_error())?;
			let trie_nodes = crate::pack_proof_from_collected::<L>(&root, &set)
				.map_err(|_e| pack_error())?;
			result.push(trie_nodes);
		}
		Ok(Flat(result, PhantomData))
	}
}

impl<L> Into<Full<L>> for FullForMerge
	where
		L: TrieLayout,
		TrieHash<L>: Codec,
{
	// TODO consider only using try into (may not be very straightforward with backend)
	fn into(self) -> Full<L> {
		self.to_full()
			.expect("Full for merge was recorded on a correct state")
	}
}

impl<L> Into<Flat<L>> for FullForMerge
	where
		L: TrieLayout,
		TrieHash<L>: Codec,
{
	fn into(self) -> Flat<L> {
		self.to_flat()
			.expect("Full for merge was recorded on a correct state")
	}
}

impl Into<super::simple::Flat> for FullForMerge
{
	fn into(self) -> super::simple::Flat {
		let mut result = ProofNodes::default();
		for (_child_info, (nodes, _root)) in self.0 {
			// TODO EMCH do not extend on first
			result.extend(nodes.0.into_iter().map(|(_k, v)| v));
		}
		super::simple::Flat(result)
	}
}

impl<L: TrieLayout> TryInto<super::simple::Flat> for Flat<L> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::simple::Flat> {
		let mut result = ProofNodes::default();
		for proof in self.0 {
			let (_root, unpacked_proof) = crate::unpack_proof::<L>(proof.as_slice())?;
			result.extend(unpacked_proof);
		}
		Ok(super::simple::Flat(result))
	}
}

impl<L: TrieLayout> TryInto<super::simple::Full> for Full<L> {
	type Error = super::Error;

	fn try_into(self) -> Result<super::simple::Full> {
		let mut result = ChildrenProofMap::default();
		for (child_info, proof) in self.0 {
			match child_info.child_type() {
				ChildType::ParentKeyId => {
					// Note that we could return roots from unpacking.
					let (_root, unpacked_proof) = crate::unpack_proof::<L>(proof.as_slice())?;
					result.insert(child_info, unpacked_proof);
				}
			}
		}
		Ok(super::simple::Full(result))
	}
}

/// Container recording trie nodes and their encoded hash.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct ProofMapTrieNodes(pub BTreeMap<Vec<u8>, DBValue>);

impl sp_std::default::Default for ProofMapTrieNodes {
	fn default() -> Self {
		ProofMapTrieNodes(Default::default())
	}
}

impl sp_std::ops::Deref for ProofMapTrieNodes {
	type Target = BTreeMap<Vec<u8>, DBValue>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl sp_std::ops::DerefMut for ProofMapTrieNodes {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<H: Hasher> HashDBRef<H, DBValue> for ProofMapTrieNodes
	where
		H::Out: Encode,
{
	fn get(&self, key: &H::Out, _prefix: hash_db::Prefix) -> Option<DBValue> {
		let key = key.encode();
		self.0.get(&key).cloned()
	}

	fn contains(&self, key: &H::Out, _prefix: hash_db::Prefix) -> bool {
		let key = key.encode();
		self.0.contains_key(&key)
	}
}
