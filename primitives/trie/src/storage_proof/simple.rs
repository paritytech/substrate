// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Trie storage proofs that are a simple collection of encoded nodes.

use super::*;
use codec::{Encode, Decode};
use sp_storage::ChildInfoProof;

/// A collection on encoded trie nodes.
pub type ProofNodes = Vec<Vec<u8>>;

/// Single flattened proof, all default child trie are flattened over a same
/// container, no child trie information is provided.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct Flat(pub(crate) ProofNodes);

/// Compacted proof with child trie organisation.
///
/// This is taking more space than the flat variant.but
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct Full(pub(crate) ChildrenProofMap<ProofNodes>);

impl Flat {
	/// Access to inner proof node,
	/// mainly needed for part of the
	/// code that is not generic or test.
	pub fn into_nodes(self) -> ProofNodes {
		self.0
	}
	/// Instantiate from inner proof node,
	/// mainly needed for part of the
	/// code that is not generic or test.
	pub fn from_nodes(nodes: ProofNodes) -> Self {
		Flat(nodes)
	}
}

impl Common for Flat {
	fn empty() -> Self {
		Flat(Default::default())
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

impl Common for Full {
	fn empty() -> Self {
		Full(Default::default())
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

impl Mergeable for Flat {
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self> {
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		for proof in proofs {
			unique_set.extend(proof.0);
		}
		Flat(unique_set.into_iter().collect())
	}
}

impl Mergeable for Full {
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self> {
		let mut child_sets = ChildrenProofMap::<BTreeSet<Vec<u8>>>::default();
		for children in proofs {
			for (child_info, child) in children.0.into_iter() {
				let set = child_sets.entry(child_info).or_default();
				set.extend(child);
			}
		}
		Full(ChildrenProofMap(child_sets
			.into_iter()
			.map(|(child_info, set)| (child_info, set.into_iter().collect()))
			.collect()))
	}
}

impl<H: Hasher> Recordable<H> for Flat {
	const INPUT_KIND: InputKind = InputKind::None;

	type RecordBackend = super::FlatRecorder<H>;

	fn extract_proof(recorder: &Self::RecordBackend, _input: Input) -> Result<Self> {
		let trie_nodes = recorder.0
			.iter()
			.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
			.collect();
		Ok(Flat(trie_nodes))
	}
}

impl<H: Hasher> Recordable<H> for Full {
	const INPUT_KIND: InputKind = InputKind::None;

	type RecordBackend = super::FullRecorder<H>;

	fn extract_proof(recorder: &Self::RecordBackend, _input: Input) -> Result<Self> {
		let mut result = ChildrenProofMap::default();
		for (child_info, set) in recorder.0.iter() {
			let trie_nodes: Vec<Vec<u8>> = set
				.iter()
				.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
				.collect();
			result.insert(child_info.proof_info(), trie_nodes);
		}
		Ok(Full(result))
	}
}

impl<H: Hasher> BackendProof<H> for Flat {
	type ProofRaw = Self;

	fn into_partial_db(self) -> Result<MemoryDB<H>> {
		use hash_db::HashDB;
		let mut db = MemoryDB::default();
		for item in self.0.into_iter() {
			db.insert(hash_db::EMPTY_PREFIX, &item[..]);
		}
		Ok(db)
	}
}

impl<H: Hasher> BackendProof<H> for Full {
	type ProofRaw = Self;

	fn into_partial_db(self) -> Result<MemoryDB<H>> {
		use hash_db::HashDB;
		let mut db = MemoryDB::default();
		for (_child_info, proof) in self.0.into_iter() {
			for item in proof.into_iter() {
				db.insert(hash_db::EMPTY_PREFIX, &item);
			}
		}

		Ok(db)
	}
}

impl<H: Hasher> FullBackendProof<H> for Full {
	fn into_partial_full_db(self) -> Result<ChildrenProofMap<MemoryDB<H>>> {
		use hash_db::HashDB;
		let mut result = ChildrenProofMap::default();
		for (child_info, proof) in self.0.into_iter() {
			let mut db = MemoryDB::default();
			for item in proof.into_iter() {
				db.insert(hash_db::EMPTY_PREFIX, &item);
			}
			result.insert(child_info, db);
		}
		Ok(result)
	}
}

// Note that this implementation is only possible
// as long as we only have default child trie which
// can be flattened into top trie storage.
impl Into<Flat> for Full {
	fn into(self) -> Flat {
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		for (child_info, nodes) in self.0 {
			assert!(matches!(child_info, ChildInfoProof::Default(..)));
			unique_set.extend(nodes);
		}
		Flat(unique_set.into_iter().collect())
	}
}

impl Into<Full> for Flat {
	fn into(self) -> Full {
		let mut result = ChildrenProofMap::default();
		result.insert(ChildInfoProof::top_trie(), self.0);
		Full(result)
	}
}

#[test]
fn flat_encoding_compatible() {
	let nodes = ProofNodes::from([vec![1u8], vec![2u8, 3u8]]);
	let flat = Flat::from_nodes(nodes.clone());
	assert_eq!(nodes.encode(), flat.encode());
}
