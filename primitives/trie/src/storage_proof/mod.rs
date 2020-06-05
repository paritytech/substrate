// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use sp_std::collections::{btree_map::BTreeMap, btree_map, btree_map::Entry};
use sp_std::collections::btree_set::BTreeSet;
#[cfg(feature = "std")]
use std::collections::hash_map::Entry as HEntry;
use sp_std::vec::Vec;
use codec::{Codec, Encode, Decode, Input as CodecInput, Output as CodecOutput, Error as CodecError};
use hash_db::{Hasher, HashDBRef};
use crate::Layout;
use sp_storage::{ChildInfo, ChildInfoProof, ChildrenMap};
use trie_db::DBValue;

#[cfg(feature = "std")]
use std::sync::Arc;
#[cfg(feature = "std")]
use parking_lot::RwLock;

pub mod simple;
pub mod compact;
pub mod query_plan;
pub mod multiple;

// We are not including it to sp_std, this hash map
// usage is restricted here to proof.
// In practice it is already use internally by no_std trie_db.
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
	Proof(&'static str),
	/// Error produce by trie manipulation.
	Trie(String),
}

#[cfg(not(feature = "std"))]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Error {
	/// Error produce by storage proof logic.
	Proof,
	/// Error produce by trie manipulation.
	Trie,
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
		// Only trie error is build from box so we use a tiny shortcut here.
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

const fn pack_error() -> Error {
	error("Error while packing for proof")
}

const fn missing_verify_input() -> Error {
	error("Input missing for proof verification")
}

const fn incompatible_type() -> Error {
	error("Incompatible type")
}


#[derive(Clone)]
/// Additional information needed for packing or unpacking storage proof.
/// These do not need to be part of the proof but are required
/// when processing the proof.
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
	/// Get input kind for a given input.
	pub fn kind(&self) -> InputKind {
		match self {
			Input::ChildTrieRoots(..) => InputKind::ChildTrieRoots,
			Input::QueryPlan(..) => InputKind::QueryPlan,
			Input::QueryPlanWithValues(..) => InputKind::QueryPlanWithValues,
			Input::None => InputKind::None,
		}
	}

	/// Updates input with new content.
	/// Return false on failure.
	/// Fails when the input type differs, except for `None` input
	/// that is always reassignable.
	///
	/// Merging query plan inputs is not allowed (unimplemented),
	/// but could be.
	#[must_use]
	pub fn consolidate(&mut self, other: Self) -> Result<()> {
		let incompatible_types = || Err(error("Incompatible types for consolidating proofs"));
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
									return Err(error("Incompatible children root when consolidating proofs"));
								},
								btree_map::Entry::Vacant(v) => {
									v.insert(root);
								},
							}
						}
					},
					Input::QueryPlan(..) => return incompatible_types(),
					Input::QueryPlanWithValues(..) => return incompatible_types(),
				}
			},
			Input::QueryPlan(..) => return incompatible_types(),
			Input::QueryPlanWithValues(..) => return incompatible_types(),
		}
		Ok(())
	}
}

/// Kind for a `Input` variant.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
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

/// Trait for proofs that can be use as a partial backend for verification.
pub trait StorageProof: sp_std::fmt::Debug + Sized + 'static {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	fn empty() -> Self;

	/// Returns whether this is an empty proof.
	fn is_empty(&self) -> bool;
}

/// Trait for proofs that can be merged.
pub trait MergeableStorageProof: StorageProof {
	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self>;
}

/// Trait for proofs that can be recorded against a trie backend.
pub trait RegStorageProof<Hash>: StorageProof {
	/// Variant of enum input to use.
	const INPUT_KIND: InputKind;

	/// The data structure for recording proof entries.
	type RecordBackend: RecordBackend<Hash>;

	/// Extracts the gathered unordered encoded trie nodes.
	/// Depending on `kind`, encoded trie nodes can change
	/// (usually to compact the proof).
	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self>;
}
/*
/// Associate a different proof kind for recording proof.
/// The recorded proof will need to be convertible to this type.
///
/// This trait is not strictly needed but ensure simple proof construction
/// rules (a single possible registration proof).
///
/// TODO EMCH really consider removing.
pub trait WithRegStorageProof<Hash>: Sized {
	/// Associated proof to register.
	type RegStorageProof: Into<Self> + RegStorageProof<Hash>;
}
*/
pub trait BackendStorageProof: Codec + StorageProof {}

/// Trait for proofs that can use to create a partial trie backend.
pub trait CheckableStorageProof: Codec + StorageProof {
	/// Run proof validation when the proof allows immediate
	/// verification.
	fn verify(self, input: &Input) -> Result<bool>;
}

/// Trie encoded node recorder.
/// TODO EMCH consider using &mut and change reg storage (consume) proof
/// to implement without rc & sync, and encapsulate from calling
/// code.
pub trait RecordBackend<Hash>: Sync + Send + Clone + Default {
	/// Access recorded value, allow using the backend as a cache.
	fn get(&self, child_info: &ChildInfo, key: &Hash) -> Option<Option<DBValue>>;
	/// Record the actual value.
	/// TODO EMCH switch to all ref or all value for param.
	fn record(&self, child_info: &ChildInfo, key: &Hash, value: Option<DBValue>);
	/// Merge two record, can fail.
	fn merge(&mut self, other: Self) -> bool;
}

#[cfg(feature = "std")]
#[derive(Clone, Default)]
/// Records are separated by child trie, this is needed for
/// proof compaction.
pub struct FullSyncRecorder<Hash>(Arc<RwLock<ChildrenMap<RecordMapTrieNodes<Hash>>>>);

#[cfg(feature = "std")]
#[derive(Clone, Default)]
/// Single storage for all recoded nodes (as in
/// state db column).
/// That this variant exists only for performance
/// (on less map access than in `Full`), but is not strictly
/// necessary.
pub struct FlatSyncRecorder<Hash>(Arc<RwLock<RecordMapTrieNodes<Hash>>>);


#[cfg(feature = "std")]
impl<Hash: Default + Clone + Eq + sp_std::hash::Hash + Send + Sync> RecordBackend<Hash> for FullSyncRecorder<Hash> {
	fn get(&self, child_info: &ChildInfo, key: &Hash) -> Option<Option<DBValue>> {
		self.0.read().get(child_info).and_then(|s| (**s).get(&key).cloned())
	}

	fn record(&self, child_info: &ChildInfo, key: &Hash, value: Option<DBValue>) {
		self.0.write().entry(child_info.clone())
			.or_default()
			.insert(key.clone(), value.clone());
	}

	fn merge(&mut self, other: Self) -> bool {
		let mut first = self.0.write();
		let mut second = other.0.write();
		for (child_info, other) in std::mem::replace(&mut *second, Default::default()) {
			match first.entry(child_info) {
				Entry::Occupied(mut entry) => {
					for (key, value) in other.0 { 
						match entry.get_mut().entry(key) {
							HEntry::Occupied(entry) => {
								if entry.get() != &value {
									return false;
								}
							},
							HEntry::Vacant(entry) => {
								entry.insert(value);
							},
						}
					}
				},
				Entry::Vacant(entry) => {
					entry.insert(other);
				},
			}
		}
		true
	}
}

#[cfg(feature = "std")]
impl<Hash: Default + Clone + Eq + sp_std::hash::Hash + Send + Sync> RecordBackend<Hash> for FlatSyncRecorder<Hash> {
	fn get(&self, _child_info: &ChildInfo, key: &Hash) -> Option<Option<DBValue>> {
		(**self.0.read()).get(&key).cloned()
	}

	fn record(&self, _child_info: &ChildInfo, key: &Hash, value: Option<DBValue>) {
		self.0.write().insert(key.clone(), value.clone());
	}

	fn merge(&mut self, other: Self) -> bool {
		let mut first = self.0.write();
		let mut second = other.0.write();
		for (key, value) in std::mem::replace(&mut *second, Default::default()).0 {
			match first.entry(key) {
				HEntry::Occupied(entry) => {
					if entry.get() != &value {
						return false;
					}
				},
				HEntry::Vacant(entry) => {
					entry.insert(value);
				},
			}
		}
		true
	}
}

/// An iterator over trie nodes constructed from a storage proof. The nodes are not guaranteed to
/// be traversed in any particular order.
pub struct StorageProofNodeIterator {
	inner: <Vec<Vec<u8>> as IntoIterator>::IntoIter,
}

impl Iterator for StorageProofNodeIterator {
	type Item = Vec<u8>;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

/// Type for storing a map of child trie proof related information.
/// A few utilities methods are defined.
#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
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
pub struct RecordMapTrieNodes<Hash>(HashMap<Hash, Option<DBValue>>);

impl<H> sp_std::default::Default for RecordMapTrieNodes<H> {
	fn default() -> Self {
		RecordMapTrieNodes(Default::default())
	}
}

impl<H> sp_std::ops::Deref for RecordMapTrieNodes<H> {
	type Target = HashMap<H, Option<DBValue>>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<H> sp_std::ops::DerefMut for RecordMapTrieNodes<H> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<H: Hasher> HashDBRef<H, DBValue> for RecordMapTrieNodes<H::Out> {
	fn get(&self, key: &H::Out, _prefix: hash_db::Prefix) -> Option<DBValue> {
		self.0.get(key).and_then(Clone::clone)
	}

	fn contains(&self, key: &H::Out, _prefix: hash_db::Prefix) -> bool {
		self.0.get(key).map(Option::is_some).unwrap_or(false)
	}
}

/// Container recording trie nodes and their encoded hash.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofMapTrieNodes(pub HashMap<Vec<u8>, DBValue>);

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
