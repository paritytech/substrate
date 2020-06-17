// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use sp_std::collections::{btree_map::BTreeMap, btree_map::Entry};
use sp_std::collections::btree_set::BTreeSet;
use sp_std::vec::Vec;
use codec::{Codec, Encode, Decode, Input as CodecInput, Output as CodecOutput, Error as CodecError};
use hash_db::{Hasher, HashDBRef};
use crate::Layout;
use sp_storage::{ChildInfo, ChildInfoProof, ChildrenMap};
use trie_db::DBValue;
use crate::MemoryDB;

pub mod simple;
pub mod compact;
pub mod query_plan;
pub mod multiple;

// We are not including it to sp_std, this hash map
// usage is restricted here to proof.
// In practice it is already use internally by no_std trie_db.
#[cfg(not(feature = "std"))]
use hashbrown::{hash_map::Entry as HEntry, HashMap};

#[cfg(feature = "std")]
use std::collections::{hash_map::Entry as HEntry, HashMap};

type Result<T> = sp_std::result::Result<T, Error>;
type CodecResult<T> = sp_std::result::Result<T, codec::Error>;

#[cfg(feature = "std")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Error {
	/// Error produced by storage proof logic.
	/// It is formatted in std to simplify type.
	Proof(&'static str),
	/// Error produced by trie manipulation.
	Trie(String),
}

#[cfg(feature = "std")]
impl std::error::Error for Error { }

#[cfg(not(feature = "std"))]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Error {
	/// Error produced by storage proof logic.
	Proof,
	/// Error produced by trie manipulation.
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
		// Only trie error is build from box so we do a tiny simplification here
		// by generalizing.
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


#[derive(Clone, Eq, PartialEq)]
/// Additional information needed to manage a storage proof.
/// These do not need to be part of the proof but are required
/// when processing the proof.
pub enum Input {
	/// Proof is self contained.
	None,

	/// Contains trie roots used during proof processing.
	ChildTrieRoots(ChildrenProofMap<Vec<u8>>),

	/// For each children, contains encoded trie roots used during proof processing.
	/// Also contains key and values queried during the proof processing.
	QueryPlanWithValues(ChildrenProofMap<(Vec<u8>, Vec<(Vec<u8>, Option<Vec<u8>>)>)>),

	/// Contains trie roots used during proof processing.
	/// Contains keys queried during the proof processing.
	QueryPlan(ChildrenProofMap<(Vec<u8>, Vec<Vec<u8>>)>),
}

impl Default for Input {
	fn default() -> Self {
		Input::None
	}
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

	/// Build a query plan with values.
	/// All tuples are key and optional value.
	/// Children iterator also contains children encoded root.
	/// If `include_child_root` is set to true, we add the child trie query to the top
	/// trie, that is usually what we want (unless we only want to prove something
	/// local to a child trie.
	pub fn query_plan_with_values(
		top_encoded_root: Vec<u8>,
		top: impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
		children: impl Iterator<Item = (
			ChildInfo,
			Vec<u8>,
			impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
		)>,
		include_child_root: bool,
	) -> Input {
		let mut result = ChildrenProofMap::default();
		let mut additional_roots = Vec::new();
		for (child_info, encoded_root, key_values) in children {
			if include_child_root {
				additional_roots.push((
					child_info.prefixed_storage_key().into_inner(),
					Some(encoded_root.clone()),
				));
			}
			result.insert(child_info.proof_info(), (encoded_root, key_values.collect()));
		}
		let mut top_values: Vec<_> = top.collect();
		top_values.extend(additional_roots);
		result.insert(ChildInfo::top_trie().proof_info(), (top_encoded_root, top_values));
		
		Input::QueryPlanWithValues(result)
	}

	/// Build a query plan.
	/// Iterator contains key.
	/// Children iterator also contains children encoded root.
	/// If `include_child_root` is set to true, we add the child trie query to the top
	/// trie, that is usually what we want (unless we only want to prove something
	/// local to a child trie.
	pub fn query_plan(
		top_encoded_root: Vec<u8>,
		top: impl Iterator<Item = Vec<u8>>,
		children: impl Iterator<Item = (ChildInfo, Vec<u8>, impl Iterator<Item = Vec<u8>>)>,
		include_child_root: bool,
	) -> Input {
		let mut result = ChildrenProofMap::default();
		let mut additional_roots = Vec::new();
		for (child_info, encoded_root, keys) in children {
			if include_child_root {
				additional_roots.push(child_info.prefixed_storage_key().into_inner());
			}
			result.insert(child_info.proof_info(), (encoded_root, keys.collect()));
		}
		let mut top_keys: Vec<_> = top.collect();
		top_keys.extend(additional_roots);
		result.insert(ChildInfo::top_trie().proof_info(), (top_encoded_root, top_keys));
		
		Input::QueryPlan(result)
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

/// Basic trait for proofs.
pub trait Common: sp_std::fmt::Debug + Sized {
	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	fn empty() -> Self;

	/// Returns whether this is an empty proof.
	fn is_empty(&self) -> bool;
}

/// Trait for proofs that can be merged.
///
/// Merging can be a non negligeable additional cost.
/// So when possible, user should rather share recording context
/// than merge multiple recorded proofs.
pub trait Mergeable: Common {
	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self>;
}

/// Trait for proofs that can be recorded against a `RecordBackend`.
pub trait Recordable<H: Hasher>: Common {
	/// Variant of enum input to use.
	const INPUT_KIND: InputKind;

	/// The data structure for recording proof entries.
	type RecordBackend: RecordBackend<H>;

	/// Extracts the gathered proof.
	/// The input provided must match the kind specified by `Recordable::INPUT_KIND`.
	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self>;
}

/// Proof that could be use as a backend to execute action
/// on a backend.
pub trait BackendProof<H: Hasher>: Codec + Common {
	/// Intermediate proof format that is recorded
	/// and mergeable.
	type ProofRaw: Recordable<H>
		+ Mergeable
		+ Into<Self>;

	/// Extract a trie db from the proof.
	/// This mainly allows running proof against
	/// a trie backend (memorydb containing unordered
	/// gathered encoded node in this case). 
	/// Can fail on invalid proof content.
	fn into_partial_db(self) -> Result<MemoryDB<H>>;
}

/// Proof that could be use as a backend to execute action
/// on a backend, with a different backend per child proofs.
pub trait FullBackendProof<H: Hasher>: BackendProof<H> {
	/// Extract a trie dbs with children info from the proof.
	/// Can fail on invalid proof content.
	fn into_partial_full_db(self) -> Result<ChildrenProofMap<MemoryDB<H>>>;
}

/// Trait for proofs that simply provides validity information.
pub trait Verifiable: Codec + Common {
	/// Run proof validation, return verification result.
	/// Error is returned for invalid input, or bad proof format.
	fn verify(self, input: &Input) -> Result<bool>;
}

/// Trie encoded node recorder trait.
///
/// This trait does not strictly need H as generic parameter and could use H::Out,
/// but currently use Hasher makes code more readable.
pub trait RecordBackend<H: Hasher>: Send + Sync + Clone + Default {
	/// Access recorded value, allow using the backend as a cache.
	fn get(&self, child_info: &ChildInfo, key: &H::Out) -> Option<Option<DBValue>>;
	/// Record the actual value.
	fn record(&mut self, child_info: ChildInfo, key: H::Out, value: Option<DBValue>);
	/// Merge two records, returns false on failure.
	fn merge(&mut self, other: Self) -> bool;
}

/// Trie node recorder with child trie isolation, keeping child trie origin
/// is needed for proof compaction.
pub struct FullRecorder<H: Hasher>(ChildrenMap<RecordMapTrieNodes<H>>);

/// Trie node recorder with a single storage for all recoded nodes (as in
/// state db column).
/// This variant exists only for performance, but is not strictly necessary.
/// (`FullRecorder` cost an additional map access)
pub struct FlatRecorder<H: Hasher>(RecordMapTrieNodes<H>);

impl<H: Hasher> Default for FlatRecorder<H> {
	fn default() -> Self {
		FlatRecorder(Default::default())
	}
}

impl<H: Hasher> Default for FullRecorder<H> {
	fn default() -> Self {
		FullRecorder(Default::default())
	}
}

impl<H: Hasher> Clone for FlatRecorder<H> {
	fn clone(&self) -> Self {
		FlatRecorder(self.0.clone())
	}
}

impl<H: Hasher> Clone for FullRecorder<H> {
	fn clone(&self) -> Self {
		FullRecorder(self.0.clone())
	}
}

impl<H: Hasher> RecordBackend<H> for FullRecorder<H> {
	fn get(&self, child_info: &ChildInfo, key: &H::Out) -> Option<Option<DBValue>> {
		self.0.get(child_info).and_then(|s| (**s).get(&key).cloned())
	}

	fn record(&mut self, child_info: ChildInfo, key: H::Out, value: Option<DBValue>) {
		self.0.entry(child_info)
			.or_default()
			.insert(key, value);
	}

	fn merge(&mut self, mut other: Self) -> bool {
		for (child_info, other) in sp_std::mem::replace(&mut other.0, Default::default()) {
			match self.0.entry(child_info) {
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

impl<H: Hasher> RecordBackend<H> for FlatRecorder<H> {
	fn get(&self, _child_info: &ChildInfo, key: &H::Out) -> Option<Option<DBValue>> {
		(*self.0).get(&key).cloned()
	}

	fn record(&mut self, _child_info: ChildInfo, key: H::Out, value: Option<DBValue>) {
		(*self.0).insert(key.clone(), value.clone());
	}

	fn merge(&mut self, mut other: Self) -> bool {
		for (key, value) in sp_std::mem::replace(&mut other.0, Default::default()).0 {
			match self.0.entry(key) {
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

/// Container recording trie nodes. TODO EMCH make it a type alias.
struct RecordMapTrieNodes<H: Hasher>(HashMap<H::Out, Option<DBValue>>);

impl<H: Hasher> sp_std::default::Default for RecordMapTrieNodes<H> {
	fn default() -> Self {
		RecordMapTrieNodes(Default::default())
	}
}

impl<H: Hasher> Clone for RecordMapTrieNodes<H> {
	fn clone(&self) -> Self {
		RecordMapTrieNodes(self.0.clone())
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
