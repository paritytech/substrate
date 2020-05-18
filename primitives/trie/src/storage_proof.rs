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

use sp_std::collections::{btree_map::BTreeMap, btree_map};
use sp_std::collections::btree_set::BTreeSet;
use sp_std::vec::Vec;
use sp_std::convert::TryInto;
use codec::{Codec, Encode, Decode, Input as CodecInput, Output as CodecOutput, Error as CodecError};
use hash_db::{Hasher, HashDB, HashDBRef, EMPTY_PREFIX};
use crate::{MemoryDB, Layout};
use sp_storage::{ChildInfoProof, ChildType, ChildrenMap};
use trie_db::DBValue;
// we are not using std as this use in no_std is
// only allowed here because it is already use in
// no_std use of trie_db.
#[cfg(not(feature = "std"))]
use hashbrown::HashMap;

#[cfg(feature = "std")]
use std::collections::HashMap;

type Result<T> = sp_std::result::Result<T, Error>;
type CodecResult<T> = sp_std::result::Result<T, codec::Error>;

#[cfg(feature = "std")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Error {
	/// Error produce by storage proof logic.
	/// It is formatted in std to simplify type.
	Trie(String),
	/// Error produce by trie manipulation.
	Proof(&'static str),
}

#[cfg(not(feature = "std"))]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Error {
	/// Error produce by storage proof logic.
	Trie,
	/// Error produce by trie manipulation.
	Proof,
}

#[cfg(feature = "std")]
impl sp_std::fmt::Display for Error {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		match self {
			Error::Trie(msg) => write!(f, "Proof error trie: {}", msg),
			Error::Proof(msg) => write!(f, "Proof error: {}", msg),
		}
	}
}

#[cfg(feature = "std")]
impl<E: sp_std::fmt::Display> sp_std::convert::From<sp_std::boxed::Box<E>> for Error {
	fn from(e: sp_std::boxed::Box<E>) -> Self {
		// currently only trie error is build from box
		Error::Trie(format!("{}", e))
	}
}

#[cfg(not(feature = "std"))]
impl<E> sp_std::convert::From<sp_std::boxed::Box<E>> for Error {
	fn from(_e: sp_std::boxed::Box<E>) -> Self {
		Error::Trie
	}
}

impl sp_std::convert::From<CodecError> for Error {
	fn from(e: CodecError) -> Self {
		error(e.what())
	}
}

#[cfg(feature = "std")]
const fn error(message: &'static str) -> Error {
	Error::Proof(message)
}

#[cfg(not(feature = "std"))]
const fn error(_message: &'static str) -> Error {
	Error::Proof
}

const fn missing_pack_input() -> Error {
	error("Packing input missing for proof")
}

const fn missing_verify_input() -> Error {
	error("Input missing for proof verification")
}

const fn no_partial_db_support() -> Error {
	error("Partial db not supported for this proof")
}

/// Different kind of proof representation are allowed.
/// This definition is used as input parameter when producing
/// a storage proof.
#[repr(u8)]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum StorageProofKind {
	/// Kind for `StorageProof::Flatten`.
	Flatten,

	/// Kind for `StorageProof::TrieSkipHashes`.
	TrieSkipHashes,

	/// Kind for `StorageProof::KnownQueryPlanAndValues`.
	KnownQueryPlanAndValues,

	/// Technical only

	/// Kind for `StorageProof::TrieSkipHashesForMerge`.
	TrieSkipHashesForMerge = 125,

	/// Testing only indices

	/// Kind for `StorageProof::Full`.
	Full = 126,

	/// Kind for `StorageProof::TrieSkipHashesFull`.
	TrieSkipHashesFull = 127,
}

impl StorageProofKind {
	/// Decode a byte value representing the storage byte.
	/// Return `None` if value does not exists.
	#[cfg(test)]
	pub fn read_from_byte(encoded: u8) -> Option<Self> {
		Some(match encoded {
			x if x == StorageProofKind::Flatten as u8 => StorageProofKind::Flatten,
			x if x == StorageProofKind::TrieSkipHashes as u8 => StorageProofKind::TrieSkipHashes,
			x if x == StorageProofKind::KnownQueryPlanAndValues as u8
				=> StorageProofKind::KnownQueryPlanAndValues,
			x if x == StorageProofKind::Full as u8 => StorageProofKind::Full,
			x if x == StorageProofKind::TrieSkipHashesFull as u8 => StorageProofKind::TrieSkipHashesFull,
			x if x == StorageProofKind::TrieSkipHashesForMerge as u8
				=> StorageProofKind::TrieSkipHashesForMerge,
			x if x == StorageProofKind::TrieSkipHashesFull as u8
				=> StorageProofKind::TrieSkipHashesFull,
			_ => return None,
		})
	}

	/// Decode a byte value representing the storage byte.
	/// Return `None` if value does not exists.
	#[cfg(not(test))]
	pub fn read_from_byte(encoded: u8) -> Option<Self> {
		Some(match encoded {
			x if x == StorageProofKind::Flatten as u8 => StorageProofKind::Flatten,
			x if x == StorageProofKind::TrieSkipHashes as u8 => StorageProofKind::TrieSkipHashes,
			x if x == StorageProofKind::KnownQueryPlanAndValues as u8
				=> StorageProofKind::KnownQueryPlanAndValues,
			_ => return None,
		})
	}
}

#[derive(Clone)]
/// Additional information needed for packing or unpacking.
/// These do not need to be part of the proof but are required
/// when using the proof.
pub enum Input {
	/// Proof is self contained.
	None,

	/// Contains trie roots used during proof processing.
	ChildTrieRoots(ChildrenProofMap<Vec<u8>>),

	/// Contains trie roots used during proof processing.
	/// Contains key and values queried during the proof processing.
	QueryPlanWithValues(ChildrenProofMap<(Vec<u8>, Vec<(Vec<u8>, Option<Vec<u8>>)>)>),

	/// Contains trie roots used during proof processing.
	/// Contains keys queried during the proof processing.
	QueryPlan(ChildrenProofMap<(Vec<u8>, Vec<Vec<u8>>)>),
}

impl Input {
	#[must_use]
	/// Update input with new content.
	/// Return false on failure.
	/// Fail when the content differs, except for `None` input
	/// that is always reassignable.
	///
	/// Not that currently all query plan input are not mergeable
	/// even if it could in the future.
	pub fn consolidate(&mut self, other: Self) -> bool {
		match self {
			Input::None => {
				*self = other;
			},
			Input::ChildTrieRoots(children) => {
				match other {
					Input::None => (),
					Input::ChildTrieRoots(children_other) => {
						for (child_info, root) in children_other {
							match children.entry(child_info) {
								btree_map::Entry::Occupied(v) => if v.get() != &root {
									return false;
								},
								btree_map::Entry::Vacant(v) => {
									v.insert(root);
								},
							}
						}
					},
					Input::QueryPlan(..) => return false,
					Input::QueryPlanWithValues(..) => return false,
				}
			},
			Input::QueryPlan(..) => return false,
			Input::QueryPlanWithValues(..) => return false,
		}
		true
	}
}

/// Kind for designing an `Input` variant.
pub enum InputKind {
	/// `Input::None` kind.
	None,

	/// `Input::ChildTrieRoots` kind.
	ChildTrieRoots,

	/// `Input::QueryPlan` kind.
	QueryPlan,

	/// `Input::QueryPlanWithValues` kind.
	QueryPlanWithValues,
}

impl StorageProofKind {
	/// Some proof variants requires more than just the collected
	/// encoded nodes.
	pub fn processing_input_kind(&self) -> InputKind {
		match self {
			StorageProofKind::KnownQueryPlanAndValues => InputKind::QueryPlan,
			StorageProofKind::TrieSkipHashesForMerge
				| StorageProofKind::TrieSkipHashes
				| StorageProofKind::TrieSkipHashesFull => InputKind::ChildTrieRoots,
			StorageProofKind::Full
				| StorageProofKind::Flatten => InputKind::None,
		}
	}

	/// Same as `need_additional_info_to_produce` but for reading.
	pub fn verify_input_kind(&self) -> InputKind {
		match self {
			StorageProofKind::KnownQueryPlanAndValues => InputKind::QueryPlanWithValues,
			StorageProofKind::TrieSkipHashes
				| StorageProofKind::TrieSkipHashesFull
				| StorageProofKind::TrieSkipHashesForMerge
				| StorageProofKind::Full
				| StorageProofKind::Flatten => InputKind::None,
		}
	}

	/// Some proof can get unpack into another proof representation.
	pub fn can_unpack(&self) -> bool {
		match self {
			StorageProofKind::KnownQueryPlanAndValues => false,
			StorageProofKind::TrieSkipHashes
				| StorageProofKind::TrieSkipHashesFull => true,
			StorageProofKind::Full
				| StorageProofKind::TrieSkipHashesForMerge
				| StorageProofKind::Flatten => false,
		}
	}

	/// Indicates if we need to record proof with splitted child trie information
	/// or can simply record on a single collection.
	pub fn need_register_full(&self) -> bool {
		match self {
			StorageProofKind::Flatten => false,
			StorageProofKind::Full
				| StorageProofKind::KnownQueryPlanAndValues
				| StorageProofKind::TrieSkipHashes
				| StorageProofKind::TrieSkipHashesForMerge
				| StorageProofKind::TrieSkipHashesFull => true,
		}
	}

	/// Indicates if we should execute proof over a backend,
	/// and if so, if the backend need to be full.
	pub fn use_full_partial_db(&self) -> Option<bool> {
		match self {
			StorageProofKind::Flatten
				| StorageProofKind::TrieSkipHashes => Some(false),
			StorageProofKind::Full
				| StorageProofKind::TrieSkipHashesForMerge
				| StorageProofKind::TrieSkipHashesFull => Some(true),
			StorageProofKind::KnownQueryPlanAndValues => None,
		}
	}

	/// Proof that should be use with `verify` method.
	pub fn can_use_verify(&self) -> bool {
		match self {
			StorageProofKind::KnownQueryPlanAndValues => true,
			_ => false,
		}
	}

	/// Can be use as a db backend for proof check and
	/// result fetch.
	/// If false `StorageProof` `as_partial_db` method
	/// failure is related to an unsupported capability.
	pub fn can_use_as_partial_db(&self) -> bool {
		match self {
			StorageProofKind::KnownQueryPlanAndValues => false,
			_ => true,
		}
	}

	/// Can be use as a db backend without child trie
	/// distinction.
	/// If false `StorageProof` `as_partial_flat_db` method
	/// failure is related to an unsupported capability.
	pub fn can_use_as_flat_partial_db(&self) -> bool {
		self.can_use_as_partial_db()
	}

	/// Return the best kind to use for merging later, and
	/// wether the merge should produce full proof, and if
	/// we are recursing.
	pub fn mergeable_kind(&self) -> (Self, bool, bool) {
		match self {
			StorageProofKind::TrieSkipHashes => (StorageProofKind::TrieSkipHashesForMerge, false, false),
			StorageProofKind::TrieSkipHashesFull => (StorageProofKind::TrieSkipHashesForMerge, true, false),
			StorageProofKind::TrieSkipHashesForMerge => (StorageProofKind::TrieSkipHashesForMerge, true, true),
			s => (*s, s.use_full_partial_db().unwrap_or(false), false)
		}
	}
}

/// A collection on encoded trie nodes.
type ProofNodes = Vec<Vec<u8>>;
/// A sorted by trie nodes order collection on encoded trie nodes
/// with possibly ommitted content or special compacted encoding.
type ProofCompacted = Vec<Vec<u8>>;

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// For default trie, the proof component consists of the set of serialized nodes in the storage trie
/// accessed when looking up the keys covered by the proof. Verifying the proof requires constructing
/// the partial trie from the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StorageProof {
	/// Single flattened proof component, all default child trie are flattened over a same
	/// container, no child trie information is provided.
	Flatten(ProofNodes),

	/// This skip encoding of hashes that are
	/// calculated when reading the structue
	/// of the trie.
	/// It requires that the proof is collected with
	/// child trie separation, will encode to struct that
	/// separate child trie but do not keep information about
	/// them (for compactness) and will therefore produce a flatten
	/// verification backend.
	TrieSkipHashes(Vec<ProofCompacted>),

	/// This skip encoding of hashes, but need to know the key
	/// values that are targetted by the operation.
	/// As `TrieSkipHashes`, it does not pack hash that can be
	/// calculated, so it requires a specific call to a custom
	/// verify function with additional input.
	/// This needs to be check for every children proofs.
	KnownQueryPlanAndValues(ChildrenProofMap<ProofCompacted>),

	// Techincal variant

	/// This is an intermediate representation that keep trace of
	/// input, in order merge into a `TrieSkipHashes` or a `TrieSkipHashesFull`
	/// proof
	TrieSkipHashesForMerge(ChildrenProofMap<(ProofMapTrieNodes, Vec<u8>)>),

	// Following variants are only for testing, they still can be use but
	// decoding is not implemented.

	///	Fully described proof, it includes the child trie individual description and split its
	///	content by child trie.
	///	Currently Full variant is unused as all our child trie kind can share a same memory db
	///	(a bit more compact).
	///	This is mainly provided for test purpose and extensibility.
	Full(ChildrenProofMap<ProofNodes>),

	/// Compact form of proofs split by child trie, this is using the same compaction as
	/// `TrieSkipHashes` but do not merge the content in a single memorydb backend.
	///	This is mainly provided for test purpose and extensibility.
	TrieSkipHashesFull(ChildrenProofMap<ProofCompacted>),
}

impl Decode for StorageProof {
	fn decode<I: CodecInput>(value: &mut I) -> CodecResult<Self> {
		let kind = value.read_byte()?;
		Ok(match StorageProofKind::read_from_byte(kind)
			.ok_or_else(|| codec::Error::from("Invalid storage kind"))? {
				StorageProofKind::Flatten => StorageProof::Flatten(Decode::decode(value)?),
				StorageProofKind::TrieSkipHashes => StorageProof::TrieSkipHashes(Decode::decode(value)?),
				StorageProofKind::KnownQueryPlanAndValues
					=> StorageProof::KnownQueryPlanAndValues(Decode::decode(value)?),
				StorageProofKind::Full => StorageProof::Full(Decode::decode(value)?),
				StorageProofKind::TrieSkipHashesForMerge
					=> return Err(codec::Error::from("Invalid storage kind")),
				StorageProofKind::TrieSkipHashesFull
					=> StorageProof::TrieSkipHashesFull(Decode::decode(value)?),
		})
	}
}

impl Encode for StorageProof {
	fn encode_to<T: CodecOutput>(&self, dest: &mut T) {
		(self.kind() as u8).encode_to(dest);
		match self {
			StorageProof::Flatten(p) => p.encode_to(dest),
			StorageProof::TrieSkipHashes(p) => p.encode_to(dest),
			StorageProof::KnownQueryPlanAndValues(p) => p.encode_to(dest),
			StorageProof::Full(p) => p.encode_to(dest),
			StorageProof::TrieSkipHashesFull(p) => p.encode_to(dest),
			StorageProof::TrieSkipHashesForMerge(..) => (),
		}
	}
}

/// This encodes the full proof capabillity under
/// legacy proof format by disabling the empty proof
/// from it (empty proof should not happen because
/// the empty trie still got a empty node recorded in
/// all its proof).
pub struct LegacyEncodeAdapter<'a>(pub &'a StorageProof);

impl<'a> Encode for LegacyEncodeAdapter<'a> {
	fn encode_to<T: CodecOutput>(&self, dest: &mut T) {
		0u8.encode_to(dest);
		self.0.encode_to(dest);
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
/// Decode variant of `LegacyEncodeAdapter`.
pub struct LegacyDecodeAdapter(pub StorageProof);

/// Allow read ahead on input.
pub struct InputRevertPeek<'a, I>(pub &'a mut &'a [u8], pub &'a mut I);

impl<'a, I: CodecInput> CodecInput for InputRevertPeek<'a, I> {
	fn remaining_len(&mut self) -> CodecResult<Option<usize>> {
		Ok(self.1.remaining_len()?.map(|l| l + self.0.len()))
	}

	fn read(&mut self, into: &mut [u8]) -> CodecResult<()> {
		let mut offset = 0;
		if self.0.len() > 0 {
			if self.0.len() > into.len() {
				into.copy_from_slice(&self.0[..into.len()]);
				*self.0 = &self.0[into.len()..];
				return Ok(());
			} else {
				into[..self.0.len()].copy_from_slice(&self.0[..]);
				*self.0 = &[][..];
				offset = self.0.len();
			}
		}
		self.1.read(&mut into[offset..])
	}

	fn read_byte(&mut self) -> CodecResult<u8> {
		if self.0.len() > 0 {
			let result = self.0[0];
			*self.0 = &self.0[1..];
			Ok(result)
		} else {
			self.1.read_byte()
		}
	}
}

impl Decode for LegacyDecodeAdapter {
	fn decode<I: CodecInput>(value: &mut I) -> CodecResult<Self> {
		let legacy = value.read_byte()?;
		Ok(if legacy == 0 {
			LegacyDecodeAdapter(Decode::decode(value)?)
		} else {
			let mut legacy = &[legacy][..];
			let mut input = InputRevertPeek(&mut legacy, value);
			LegacyDecodeAdapter(StorageProof::Flatten(Decode::decode(&mut input)?))
		})
	}
}

impl StorageProof {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	pub fn empty() -> Self {
		// we default to flatten for compatibility
		Self::empty_for(StorageProofKind::Flatten)
	}

	/// Returns a new empty proof of a given kind.
	pub fn empty_for(kind: StorageProofKind) -> Self {
		match kind {
			StorageProofKind::Flatten => StorageProof::Flatten(Default::default()),
			StorageProofKind::Full => StorageProof::Full(ChildrenProofMap::default()),
			StorageProofKind::TrieSkipHashesFull => StorageProof::TrieSkipHashesFull(ChildrenProofMap::default()),
			StorageProofKind::TrieSkipHashesForMerge => StorageProof::TrieSkipHashesForMerge(
				ChildrenProofMap::default(),
			),
			StorageProofKind::KnownQueryPlanAndValues => StorageProof::KnownQueryPlanAndValues(ChildrenProofMap::default()),
			StorageProofKind::TrieSkipHashes => StorageProof::TrieSkipHashes(Default::default()),
		}
	}

	/// Returns whether this is an empty proof.
	pub fn is_empty(&self) -> bool {
		match self {
			StorageProof::Flatten(data) => data.is_empty(),
			StorageProof::Full(data) => data.is_empty(),
			StorageProof::KnownQueryPlanAndValues(data) => data.is_empty(),
			StorageProof::TrieSkipHashes(data) => data.is_empty(),
			StorageProof::TrieSkipHashesFull(data) => data.is_empty(),
			StorageProof::TrieSkipHashesForMerge(data) => data.is_empty(),
		}
	}

	/// Create an iterator over trie nodes constructed from the proof. The nodes are not guaranteed
	/// to be traversed in any particular order.
	/// This iterator is only for `Flatten` proofs, other kind of proof will return an iterator with
	/// no content.
	pub fn iter_nodes_flatten(self) -> StorageProofNodeIterator {
		StorageProofNodeIterator::new(self)
	}

	fn trie_skip_unpack<H: Hasher>(
		self,
	) -> Result<Self>
		where H::Out: Codec,
	{
		match self {
			StorageProof::TrieSkipHashesFull(children) => {
				let mut result = ChildrenProofMap::default();
				for (child_info, proof) in children {
					match child_info.child_type() {
						ChildType::ParentKeyId => {
							// Note that we could return roots from unpacking.
							let (_root, unpacked_proof) = crate::unpack_proof::<Layout<H>>(proof.as_slice())?;
							result.insert(child_info, unpacked_proof);
						}
					}
				}
				Ok(StorageProof::Full(result))
			},
			StorageProof::TrieSkipHashes(children) => {
				let mut result = ProofNodes::default();
				for proof in children {
					let (_root, unpacked_proof) = crate::unpack_proof::<Layout<H>>(proof.as_slice())?;
					result.extend(unpacked_proof);
				}

				Ok(StorageProof::Flatten(result))
			},
			s => Ok(s),
		}
	}

	/// This run proof validation when the proof allows immediate
	/// verification (`StorageProofKind::can_use_verify`).
	pub fn verify<H: Hasher>(
		self,
		input: &Input,
	) -> Result<Option<bool>>
		where H::Out: Codec,
	{
		match self {
			StorageProof::KnownQueryPlanAndValues(proof_children) => {
				if let Input::QueryPlanWithValues(input_children) = input {
					let mut root_hash = H::Out::default();
					for (child_info, nodes) in proof_children.iter() {
						if let Some((root, input)) = input_children.get(child_info) {
							// Layout h is the only supported one at the time being
							if root.len() != root_hash.as_ref().len() {
								return Ok(Some(false));
							}
							root_hash.as_mut().copy_from_slice(&root[..]);
							if let Err(_) = trie_db::proof::verify_proof::<Layout<H>, _, _, _>(
								&root_hash,
								&nodes[..],
								input.iter(),
							) {
								return Ok(Some(false));
							}
						} else {
							return Err(missing_verify_input());
						}
					}
					Ok(Some(true))
				} else {
					Err(missing_verify_input())
				}
			},
			_ => Ok(None),
		}
	}

	/// This produce the proof from collected information.
	pub fn extract_proof<H: Hasher>(
		collected: &ChildrenMap<RecordMapTrieNodes<H>>,
		kind: StorageProofKind,
		input: &Input,
	) -> Result<Self>
		where H::Out: Codec,
	{
		Ok(match kind {
			StorageProofKind::Flatten => {
				let mut result = Vec::new();
				collected.iter().for_each(|(child_info, proof)| {
					match child_info.child_type() {
						ChildType::ParentKeyId => {
							// this can get merged with top, we do not use key prefix
							result.extend(proof.0.clone()
								.drain()
								.filter_map(|(_k, v)| v)
							);
						}
					}
				});
				StorageProof::Flatten(result)
			},
			StorageProofKind::Full => {
				let mut result = ChildrenProofMap::default();
				for (child_info, set) in collected.iter() {
					let trie_nodes: Vec<Vec<u8>> = set
						.iter()
						.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
						.collect();
					result.insert(child_info.proof_info(), trie_nodes);
				}
				StorageProof::Full(result)
			},
			StorageProofKind::TrieSkipHashesForMerge => {
				if let Input::ChildTrieRoots(roots) = input {
					let mut result = ChildrenProofMap::default();
					for (child_info, set) in collected.iter() {
						let root = roots.get(&child_info.proof_info())
							.ok_or_else(|| missing_pack_input())?.clone();
						let trie_nodes: HashMap<_, _> = set
							.iter()
							.filter_map(|(k, v)| v.as_ref().map(|v| (k.encode(), v.to_vec())))
							.collect();
						result.insert(child_info.proof_info(), (ProofMapTrieNodes(trie_nodes), root));
					}
					StorageProof::TrieSkipHashesForMerge(result)
				} else {
					return Err(missing_pack_input());
				}
			},
			StorageProofKind::TrieSkipHashesFull => {
				if let Input::ChildTrieRoots(roots) = input {
					let mut result = ChildrenProofMap::default();
					for (child_info, set) in collected.iter() {
						let root = roots.get(&child_info.proof_info())
							.and_then(|r| Decode::decode(&mut &r[..]).ok())
							.ok_or_else(|| missing_pack_input())?;
						let trie_nodes = crate::pack_proof_from_collected::<Layout<H>>(&root, set)?;
						result.insert(child_info.proof_info(), trie_nodes);
					}
					StorageProof::TrieSkipHashesFull(result)
				} else {
					return Err(missing_pack_input());
				}
			},
			StorageProofKind::TrieSkipHashes => {
				if let Input::ChildTrieRoots(roots) = input {
					let mut result = Vec::default();
					for (child_info, set) in collected.iter() {
						let root = roots.get(&child_info.proof_info())
							.and_then(|r| Decode::decode(&mut &r[..]).ok())
							.ok_or_else(|| missing_pack_input())?;
						let trie_nodes = crate::pack_proof_from_collected::<Layout<H>>(&root, set)?;
						result.push(trie_nodes);
					}
					StorageProof::TrieSkipHashes(result)
				} else {
					return Err(missing_pack_input());
				}
			},
			StorageProofKind::KnownQueryPlanAndValues => {
				if let Input::QueryPlan(input_children) = input {
					let mut result = ChildrenProofMap::default();
					let mut root_hash = H::Out::default();
					for (child_info, set) in collected.iter() {
						let child_info_proof = child_info.proof_info();
						if let Some((root, keys)) = input_children.get(&child_info_proof) {
							// Layout h is the only supported one at the time being
							if root.len() != root_hash.as_ref().len() {
								return Err(missing_pack_input());
							}
							root_hash.as_mut().copy_from_slice(&root[..]);
							let trie = <trie_db::TrieDB<Layout<H>>>::new(set, &root_hash)?;
							let compacted = trie_db::proof::generate_proof(&trie, keys)?;
							result.insert(child_info_proof, compacted);
						} else {
							return Err(missing_pack_input());
						}
					}
					StorageProof::KnownQueryPlanAndValues(result)
				} else {
					return Err(missing_pack_input());
				}
			},
		})
	}

	/// This produce the proof from collected information on a flat backend.
	pub fn extract_proof_from_flat<H: Hasher>(
		collected: &RecordMapTrieNodes<H>,
		kind: StorageProofKind,
		_input: &Input,
	) -> Result<Self>
		where H::Out: Codec,
	{
		Ok(match kind {
			StorageProofKind::Flatten => {
				let trie_nodes = collected
					.iter()
					.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec()))
					.collect();
				StorageProof::Flatten(trie_nodes)
			},
			_ => return Err(no_partial_db_support()),
		})
	}

	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	/// Merge to `Flatten` if one of the item is flatten (we cannot unflatten), if not `Flatten` we output to
	/// non compact form.
	/// The function cannot pack back proof as it does not have reference to additional information
	/// needed. So for this the additional information need to be merged separately and the result
	/// of this merge be packed with it afterward.
	pub fn merge<H, I>(proofs: I, prefer_full: bool, recurse: bool) -> Result<StorageProof>
		where
			I: IntoIterator<Item=StorageProof>,
			H: Hasher,
			H::Out: Codec,
	{
		let mut do_flatten = !prefer_full;
		let mut child_sets = ChildrenProofMap::<BTreeSet<Vec<u8>>>::default();
		let mut unique_set = BTreeSet::<Vec<u8>>::default();
		let mut packable_child_sets: Option<ChildrenProofMap<(ProofMapTrieNodes, Vec<u8>)>> = None;
		// lookup for best encoding
		for mut proof in proofs {
			// unpack
			match &proof {
				&StorageProof::TrieSkipHashesFull(..) => {
					proof = proof.trie_skip_unpack::<H>()?;
				},
				&StorageProof::TrieSkipHashes(..) => {
					proof = proof.trie_skip_unpack::<H>()?;
				},
				&StorageProof::KnownQueryPlanAndValues(..) => {
					return Err(error("Proof incompatibility for merging"));
				},
				_ => (),
			}
			let proof = proof;
			match proof {
				StorageProof::TrieSkipHashesForMerge(proof) => {
					if !child_sets.is_empty() || !unique_set.is_empty() {
						return Err(error("Proof incompatibility for merging"));
					}
					if let Some(p) = packable_child_sets.as_mut() {
						for (child_info, (mut proof, root)) in proof.into_iter() {
							p.entry(child_info)
								.and_modify(|entry| {
									debug_assert!(&root == &entry.1);
									entry.0.extend(proof.drain());
								})
								.or_insert((proof, root));
						}
					} else {
						packable_child_sets = Some(proof);
					}
				},
				StorageProof::TrieSkipHashesFull(..)
					| StorageProof::TrieSkipHashes(..)
					| StorageProof::KnownQueryPlanAndValues(..)
					=> unreachable!("Unpacked or early return earlier"),
				StorageProof::Flatten(proof) => {
					if packable_child_sets.is_some() {
						return Err(error("Proof incompatibility for merging"));
					}
					if !do_flatten {
						do_flatten = true;
						for (_, set) in sp_std::mem::replace(&mut child_sets, Default::default()).into_iter() {
							unique_set.extend(set);
						}
					}
					unique_set.extend(proof);
				},
				StorageProof::Full(children) => {
					if packable_child_sets.is_some() {
						return Err(error("Proof incompatibility for merging"));
					}
					for (child_info, child) in children.into_iter() {
						if do_flatten {
							unique_set.extend(child);
						} else {
							let set = child_sets.entry(child_info).or_default();
							set.extend(child);
						}
					}
				},
			}
		}
		if let Some(children) = packable_child_sets {
			if recurse {
				return Ok(StorageProof::TrieSkipHashesForMerge(children))
			}
			if prefer_full {
				let mut result = ChildrenProofMap::default();
				for (child_info, (set, root)) in children.into_iter() {
					let root = Decode::decode(&mut &root[..])?;
					let trie_nodes = crate::pack_proof_from_collected::<Layout<H>>(&root, &set)?;
					result.insert(child_info, trie_nodes);
				}
				return Ok(StorageProof::TrieSkipHashesFull(result))
			} else {
				let mut result = Vec::default();
				for (_child_info, (set, root)) in children.iter() {
					let root = Decode::decode(&mut &root[..])?;
					let trie_nodes = crate::pack_proof_from_collected::<Layout<H>>(&root, &*set)?;
					result.push(trie_nodes);
				}
				return Ok(StorageProof::TrieSkipHashes(result))
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

	/// Get kind description for the storage proof variant.
	pub fn kind(&self) -> StorageProofKind {
		match self {
			StorageProof::Flatten(_) => StorageProofKind::Flatten,
			StorageProof::TrieSkipHashes(_) => StorageProofKind::TrieSkipHashes,
			StorageProof::KnownQueryPlanAndValues(_) => StorageProofKind::KnownQueryPlanAndValues,
			StorageProof::Full(_) => StorageProofKind::Full,
			StorageProof::TrieSkipHashesFull(_) => StorageProofKind::TrieSkipHashesFull,
			StorageProof::TrieSkipHashesForMerge(_) => StorageProofKind::TrieSkipHashesForMerge,
		}
	}

	/// Create in-memory storage of proof check backend.
	/// Currently child trie are all with same backend
	/// implementation, therefore using
	/// `as_partial_flat_db` is prefered.
	pub fn as_partial_db<H>(self) -> Result<ChildrenProofMap<MemoryDB<H>>>
	where
		H: Hasher,
		H::Out: Decode,
	{
		let mut result = ChildrenProofMap::default();
		match self {
			s@StorageProof::Flatten(..) => {
				let db = s.as_partial_flat_db::<H>()?;
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
			StorageProof::TrieSkipHashesForMerge(children) => {
				for (child_info, (proof, _root)) in children.into_iter() {
					let mut db = MemoryDB::default();
					for (key, value) in proof.0.into_iter() {
						let key = Decode::decode(&mut &key[..])?;
						db.emplace(key, EMPTY_PREFIX, value);
					}
					result.insert(child_info, db);
				}
			},
			StorageProof::TrieSkipHashesFull(children) => {
				for (child_info, proof) in children.into_iter() {
					// Note that this does check all hashes so using a trie backend
					// for further check is not really good (could use a direct value backend).
					let (_root, db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					result.insert(child_info, db);
				}
			},
			s@StorageProof::TrieSkipHashes(..) => {
				let db = s.as_partial_flat_db::<H>()?;
				result.insert(ChildInfoProof::top_trie(), db);
			},
			StorageProof::KnownQueryPlanAndValues(_children) => {
				return Err(no_partial_db_support());
			},
		}
		Ok(result)
	}

	/// Create in-memory storage of proof check backend.
	pub fn as_partial_flat_db<H>(self) -> Result<MemoryDB<H>>
	where
		H: Hasher,
		H::Out: Decode,
	{
		let mut db = MemoryDB::default();
		let mut db_empty = true;
		match self {
			s@StorageProof::Flatten(..) => {
				for item in s.iter_nodes_flatten() {
					db.insert(EMPTY_PREFIX, &item[..]);
				}
			},
			StorageProof::Full(children) => {
				for (_child_info, proof) in children.into_iter() {
					for item in proof.into_iter() {
						db.insert(EMPTY_PREFIX, &item);
					}
				}
			},
			StorageProof::TrieSkipHashesForMerge(children) => {
				for (_child_info, (proof, _root)) in children.into_iter() {
					for (key, value) in proof.0.into_iter() {
						let key = Decode::decode(&mut &key[..])?;
						db.emplace(key, EMPTY_PREFIX, value);
					}
				}
			},
			StorageProof::TrieSkipHashesFull(children) => {
				for (_child_info, proof) in children.into_iter() {
					// Note that this does check all hashes so using a trie backend
					// for further check is not really good (could use a direct value backend).
					let (_root, child_db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					if db_empty {
						db_empty = false;
						db = child_db;
					} else {
						db.consolidate(child_db);
					}
				}
			},
			StorageProof::TrieSkipHashes(children) => {
				for proof in children.into_iter() {
					let (_root, child_db) = crate::unpack_proof_to_memdb::<Layout<H>>(proof.as_slice())?;
					if db_empty {
						db_empty = false;
						db = child_db;
					} else {
						db.consolidate(child_db);
					}
				}
			},
			StorageProof::KnownQueryPlanAndValues(_children) => {
				return Err(no_partial_db_support());
			},
		}
		Ok(db)
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

impl<H: Hasher> TryInto<MemoryDB<H>> for StorageProof
	where
		H::Out: Decode,
{
	type Error = Error;

	fn try_into(self) -> Result<MemoryDB<H>> {
		self.as_partial_flat_db()
	}
}

impl<H: Hasher> TryInto<ChildrenProofMap<MemoryDB<H>>> for StorageProof
	where
		H::Out: Decode,
{
	type Error = Error;

	fn try_into(self) -> Result<ChildrenProofMap<MemoryDB<H>>> {
		self.as_partial_db()
	}
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


/// Container recording trie nodes.
#[derive(Clone)]
pub struct RecordMapTrieNodes<H: Hasher>(HashMap<H::Out, Option<DBValue>>);

/// Container recording trie nodes and their encoded hash.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofMapTrieNodes(pub HashMap<Vec<u8>, DBValue>);

impl<H: Hasher> sp_std::default::Default for RecordMapTrieNodes<H> {
	fn default() -> Self {
		RecordMapTrieNodes(Default::default())
	}
}

impl<H: Hasher> sp_std::ops::Deref for RecordMapTrieNodes<H> {
	type Target = HashMap<H::Out, Option<DBValue>>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<H: Hasher> sp_std::ops::DerefMut for RecordMapTrieNodes<H> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<H: Hasher> HashDBRef<H, DBValue> for RecordMapTrieNodes<H> {
	fn get(&self, key: &H::Out, _prefix: hash_db::Prefix) -> Option<DBValue> {
		self.0.get(key).and_then(Clone::clone)
	}

	fn contains(&self, key: &H::Out, _prefix: hash_db::Prefix) -> bool {
		self.0.get(key).map(Option::is_some).unwrap_or(false)
	}
}

impl sp_std::default::Default for ProofMapTrieNodes {
	fn default() -> Self {
		ProofMapTrieNodes(Default::default())
	}
}

impl sp_std::ops::Deref for ProofMapTrieNodes {
	type Target = HashMap<Vec<u8>, DBValue>;

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

#[test]
fn legacy_proof_codec() {
	// random content for proof, we test serialization
	let content = vec![b"first".to_vec(), b"second".to_vec()];

	let proof = StorageProof::Flatten(content.clone());
	let encoded_proof = proof.encode();

	// test adapter
	let encoded_adapter = LegacyEncodeAdapter(&proof).encode();

	assert_eq!(StorageProof::decode(&mut &encoded_proof[..]).unwrap(), proof);
	assert_eq!(encoded_adapter[0], 0);
	assert_eq!(&encoded_adapter[1..], &encoded_proof[..]);

	let adapter_proof = LegacyDecodeAdapter(proof);
	assert_eq!(LegacyDecodeAdapter::decode(&mut &encoded_adapter[..]).unwrap(), adapter_proof);
}
