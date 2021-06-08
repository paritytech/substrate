// This file is part of Substrate.

// Copyright (C) 2015-2021 Parity Technologies (UK) Ltd.
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

//! Utility functions to interact with Substrate's Base-16 Modified Merkle Patricia tree ("trie").

#![cfg_attr(not(feature = "std"), no_std)]

mod error;
mod node_header;
mod node_codec;
mod storage_proof;
mod trie_stream;

use sp_std::{boxed::Box, marker::PhantomData, vec, vec::Vec, borrow::Borrow, fmt};
use hash_db::{Hasher, Prefix};
//use trie_db::proof::{generate_proof, verify_proof};
pub use trie_db::proof::VerifyError;
/// Our `NodeCodec`-specific error.
pub use error::Error;
/// The Substrate format implementation of `TrieStream`.
pub use trie_stream::TrieStream;
/// The Substrate format implementation of `NodeCodec`.
pub use node_codec::NodeCodec;
pub use storage_proof::StorageProof;
/// Various re-exports from the `trie-db` crate.
pub use trie_db::{
	Trie, TrieMut, DBValue, Recorder, CError, Query, TrieLayout, TrieConfiguration,
	nibble_ops, TrieDBIterator, TrieDBKeyIterator, Meta, node::{NodePlan, ValuePlan},
	GlobalMeta,
};
/// Various re-exports from the `memory-db` crate.
pub use memory_db::KeyFunction;
pub use memory_db::prefixed_key;
/// Various re-exports from the `hash-db` crate.
pub use hash_db::{HashDB as HashDBT, EMPTY_PREFIX, MetaHasher};
pub use hash_db::NoMeta;

/// Meta use by trie state.
#[derive(Default, Clone, Debug)]
pub struct TrieMeta {
	/// Range of encoded value or hashed value.
	pub range: Option<core::ops::Range<usize>>,
	/// Defined in the trie layout, when used with
	/// `TrieDbMut` it switch nodes to alternative hashing
	/// method by setting `do_value_hash` to true.
	/// TODO may be useless (indicate that previous hash is
	/// not using `do_value_hash`).
	pub switch_to_value_hash: bool,
	/// When `do_value_hash` is true, try to
	/// store this behavior in top node
	/// encoded (need to be part of state).
	/// TODO remove
	pub recorded_do_value_hash: bool,
	/// Does current encoded contains a hash instead of
	/// a value (information stored in meta for proofs).
	pub contain_hash: bool,
	/// Flag indicating if alternative value hash can run.
	/// This is read and written as a state meta of the node.
	/// TODO replace by TrieDbMut node variant
	/// TODO replace by Option<usize> being size treshold.
	pub do_value_hash: bool,
	/// Record if a value was accessed, this is
	/// set as accessed by defalult, but can be
	/// change on access explicitely: `HashDB::get_with_meta`.
	/// and reset on access explicitely: `HashDB::access_from`.
	/// TODO!! remove from meta: only use in proof recorder context.
	pub unused_value: bool,
	/// Indicate that a node is using old hash scheme.
	/// TODO remove
	pub old_hash: bool,
}

impl Meta for TrieMeta {
	/// When true apply inner hashing of value.
	type GlobalMeta = bool;

	/// When true apply inner hashing of value.
	type StateMeta = bool;

	fn set_state_meta(&mut self, state_meta: Self::StateMeta) {
		if !self.do_value_hash && state_meta {
			self.do_value_hash = true;
		}
	}

	// TODO remove upstream
	fn extract_global_meta(&self) -> Self::GlobalMeta {
		self.switch_to_value_hash || self.do_value_hash
	}

	fn set_global_meta(&mut self, global_meta: Self::GlobalMeta) {
		if !self.do_value_hash && global_meta {
			self.switch_to_value_hash = true;
			self.do_value_hash = true;
		}
	}

	// TODO remove upstream?
	fn has_state_meta(&self) -> bool {
		self.do_value_hash && !self.switch_to_value_hash
	}

	// TODO consider removal upstream of this method (node type in codec)
	fn read_state_meta(&mut self, _data: &[u8]) -> Result<usize, &'static str> {
		unreachable!()
		// TODO read directly from codec.
/*		let offset = if data[0] == trie_constants::ENCODED_META_ALLOW_HASH {
			self.recorded_do_value_hash = true;
			self.do_value_hash = true;
			1
		} else {
			0
		};
		Ok(offset)*/
	}

	// TODO consider removal upstream of this method (node type in codec)
	// `do_value_hash` method is enough function to write with codec.
	fn write_state_meta(&self) -> Vec<u8> {
		unreachable!()
/*		if self.do_value_hash {
			// Note that this only works with sp_trie codec.
			// Acts as a boolean result.
			[trie_constants::ENCODED_META_ALLOW_HASH].to_vec()
		} else {
			Vec::new()
		}*/
	}

	fn meta_for_new(
		global: Self::GlobalMeta,
	) -> Self {
		let mut result = Self::default();
		result.set_global_meta(global);
		result
	}

	fn meta_for_existing_inline_node(
		global: Self::GlobalMeta,
	) -> Self {
		Self::meta_for_new(global)
	}

	// TODO meta for empty is unused: can consider removal upstream.
	fn meta_for_empty(
		global: Self::GlobalMeta,
	) -> Self {
		Self::meta_for_new(global)
	}

	// TODO if removing all meta, the Option<ValueRange> will replace it.
	fn encoded_value_callback(
		&mut self,
		value_plan: ValuePlan,
	) {
		let (contain_hash, range) = match value_plan {
			ValuePlan::Value(range) => (false, range),
			ValuePlan::HashedValue(range, _size) => (true, range),
			ValuePlan::NoValue => return,
		};

		self.range = Some(range);
		self.contain_hash = contain_hash;
		if self.switch_to_value_hash {
			// Switched value hashing.
			self.switch_to_value_hash = false
		}
	}

	fn decoded_callback(
		&mut self,
		node_plan: &NodePlan,
	) {
		let (contain_hash, range) = match node_plan.value_plan() {
			Some(ValuePlan::Value(range)) => (false, range.clone()),
			Some(ValuePlan::HashedValue(range, _size)) => (true, range.clone()),
			Some(ValuePlan::NoValue) => return,
			None => return,
		};

		self.range = Some(range);
		self.contain_hash = contain_hash;
	}

	fn contains_hash_of_value(&self) -> bool {
		self.contain_hash
	}

	// TODO could be rename to get_state_meta
	fn do_value_hash(&self) -> bool {
		self.do_value_hash
	}
}

impl TrieMeta {
	/// Was value accessed.
	pub fn accessed_value(&mut self) -> bool {
		!self.unused_value
	}

	/// For proof, this allow setting node as unaccessed until
	/// a call to `access_from`.
	pub fn set_accessed_value(&mut self, accessed: bool) {
		self.unused_value = !accessed;
	}
}

/// substrate trie layout
pub struct Layout<H, M>(bool, sp_std::marker::PhantomData<(H, M)>);

impl<H, M> fmt::Debug for Layout<H, M> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("Layout").finish()
	}
}

impl<H, M> Clone for Layout<H, M> {
	fn clone(&self) -> Self {
		Layout(self.0, sp_std::marker::PhantomData)
	}
}

impl<H, M> Default for Layout<H, M> {
	fn default() -> Self {
		Layout(false, sp_std::marker::PhantomData)
	}
}
impl<H, M> Layout<H, M> {
	/// Layout with inner hashing active.
	/// Will flag trie for hashing.
	/// TODO rename inner -> alt
	pub fn with_inner_hashing() -> Self {
		Layout(true, sp_std::marker::PhantomData)
	}
}

impl<H, M> TrieLayout for Layout<H, M>
	where
		H: Hasher,
		M: MetaHasher<H, DBValue, GlobalMeta = bool>,
		M::Meta: Meta<GlobalMeta = bool, StateMeta = bool>,
{
	const USE_EXTENSION: bool = false;
	const ALLOW_EMPTY: bool = true;
	const USE_META: bool = true;
	const READ_ROOT_STATE_META: bool = false; // TODO rem

	type Hash = H;
	type Codec = NodeCodec<Self::Hash>;
	type MetaHasher = M;
	type Meta = M::Meta;

	fn layout_meta(&self) -> GlobalMeta<Self> {
		self.0
	}

	// TODO remove upstream
	fn initialize_from_root_meta(&mut self, _root_meta: &Self::Meta) {
		unreachable!()
		/*if root_meta.extract_global_meta() {
			self.0 = true;
		}*/
	}

	// TODO remove upstream
	fn set_root_meta(_root_meta: &mut Self::Meta, _global_meta: GlobalMeta<Self>) {
		unreachable!()
//		root_meta.set_global_meta(global_meta);
	}
}

/// Hasher with support to meta.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StateHasher;

impl<H> MetaHasher<H, DBValue> for StateHasher
	where
		H: Hasher,
{
	type Meta = TrieMeta;
	type GlobalMeta = bool;

	fn hash(value: &[u8], meta: &Self::Meta) -> H::Out {
		match &meta {
			TrieMeta { range: Some(range), contain_hash: false, do_value_hash: true, switch_to_value_hash: false, .. } => {
				if range.end - range.start >= trie_constants::INNER_HASH_TRESHOLD {
					let value = inner_hashed_value::<H>(value, Some((range.start, range.end)));
					H::hash(value.as_slice())
				} else {
					H::hash(value)
				}
			},
			TrieMeta { range: Some(_range), contain_hash: true, .. } => {
				// value contains a hash of data (already inner_hashed_value).
				H::hash(value)
			},
			_ => {
				H::hash(value)
			},
		}
	}

	// TODO if removing meta upstream, still need to get DEAD_HEADER_META_HASHED_VALUE
	// from proof.
	fn stored_value(value: &[u8], mut meta: Self::Meta) -> DBValue {
		let mut stored = Vec::with_capacity(value.len() + 1);
		if meta.contain_hash {
			// already contain hash, just flag it.
			stored.push(trie_constants::DEAD_HEADER_META_HASHED_VALUE);
			stored.extend_from_slice(value);
			return stored;
		}
		if meta.unused_value {
			if let Some(range) = meta.range.as_ref() {
				if range.end - range.start >= trie_constants::INNER_HASH_TRESHOLD {
					// Waring this assume that encoded value does not start by this, so it is tightly coupled
					// with the header type of the codec: only for optimization.
					stored.push(trie_constants::DEAD_HEADER_META_HASHED_VALUE);
					let range = meta.range.as_ref().expect("Tested in condition");
					meta.contain_hash = true; // useless but could be with meta as &mut
					// store hash instead of value.
					let value = inner_hashed_value::<H>(value, Some((range.start, range.end)));
					stored.extend_from_slice(value.as_slice());
					return stored;
				}
			}
		}
		stored.extend_from_slice(value);
		stored
	}

	fn stored_value_owned(value: DBValue, meta: Self::Meta) -> DBValue {
		<Self as MetaHasher<H, DBValue>>::stored_value(value.as_slice(), meta)
	}

	// TODO remove upstream?
	fn extract_value(mut stored: &[u8], global_meta: Self::GlobalMeta) -> (&[u8], Self::Meta) {
		let input = &mut stored;
		let mut contain_hash = false;
		if input.get(0) == Some(&trie_constants::DEAD_HEADER_META_HASHED_VALUE) {
			contain_hash = true;
			*input = &input[1..];
		}
		let mut meta = TrieMeta {
			range: None,
			unused_value: contain_hash,
			contain_hash,
			do_value_hash: false,
			recorded_do_value_hash: false,
			switch_to_value_hash: false,
			old_hash: false,
		};
		meta.set_global_meta(global_meta);
		(stored, meta)
	}

	// TODO remove upstream
	fn extract_value_owned(mut stored: DBValue, global: Self::GlobalMeta) -> (DBValue, Self::Meta) {
		let len = stored.len();
		let (v, meta) = <Self as MetaHasher<H, DBValue>>::extract_value(stored.as_slice(), global);
		let removed = len - v.len();
		(stored.split_off(removed), meta)
	}
}

/// Reimplement `NoMeta` `MetaHasher` with
/// additional constraint.
/// TODO remove the MetaHasher is ignored
/// when no node have do_value_hash or layout defines it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NoMetaHasher;

impl<H> MetaHasher<H, DBValue> for NoMetaHasher 
	where
		H: Hasher,
{
	type Meta = TrieMeta;
	type GlobalMeta = bool;

	fn hash(value: &[u8], _meta: &Self::Meta) -> H::Out {
		H::hash(value)
	}

	fn stored_value(value: &[u8], _meta: Self::Meta) -> DBValue {
		value.to_vec()
	}

	fn stored_value_owned(value: DBValue, _meta: Self::Meta) -> DBValue {
		value
	}

	fn extract_value(stored: &[u8], _meta: Self::GlobalMeta) -> (&[u8], Self::Meta) {
		(stored, Default::default())
	}

	fn extract_value_owned(stored: DBValue, _meta: Self::GlobalMeta) -> (DBValue, Self::Meta) {
		(stored, Default::default())
	}
}

impl<H, M> TrieConfiguration for Layout<H, M>
	where
		H: Hasher,
		M: MetaHasher<H, DBValue, GlobalMeta = bool>,
		M::Meta: Meta<GlobalMeta = bool, StateMeta = bool>,
{
	fn trie_root<I, A, B>(&self, input: I) -> <Self::Hash as Hasher>::Out where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
	{
		trie_root::trie_root_no_extension::<H, M, TrieStream, _, _, _>(input, self.layout_meta())
	}

	fn trie_root_unhashed<I, A, B>(&self, input: I) -> Vec<u8> where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
	{
		trie_root::unhashed_trie_no_extension::<H, M, TrieStream, _, _, _>(input, self.layout_meta())
	}

	fn encode_index(input: u32) -> Vec<u8> {
		codec::Encode::encode(&codec::Compact(input))
	}
}

#[cfg(not(feature = "memory-tracker"))]
type MemTracker = memory_db::NoopTracker<trie_db::DBValue>;
#[cfg(feature = "memory-tracker")]
type MemTracker = memory_db::MemCounter<trie_db::DBValue>;

/// TrieDB error over `TrieConfiguration` trait.
pub type TrieError<L> = trie_db::TrieError<TrieHash<L>, CError<L>>;
/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
pub trait AsHashDB<H: Hasher, M, GM>: hash_db::AsHashDB<H, trie_db::DBValue, M, GM> {}
impl<H: Hasher, M, GM, T: hash_db::AsHashDB<H, trie_db::DBValue, M, GM>> AsHashDB<H, M, GM> for T {}
/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
pub type HashDB<'a, H, M, GM> = dyn hash_db::HashDB<H, trie_db::DBValue, M, GM> + 'a;
/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
/// This uses a `KeyFunction` for prefixing keys internally (avoiding
/// key conflict for non random keys).
pub type PrefixedMemoryDB<H> = memory_db::MemoryDB<
	H, memory_db::PrefixedKey<H>, trie_db::DBValue, StateHasher, MemTracker
>;
/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
/// This uses a noops `KeyFunction` (key addressing must be hashed or using
/// an encoding scheme that avoid key conflict).
pub type MemoryDB<H> = memory_db::MemoryDB<
	H, memory_db::HashKey<H>, trie_db::DBValue, StateHasher, MemTracker,
>;
/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
/// This uses a noops `KeyFunction` (key addressing must be hashed or using
/// an encoding scheme that avoid key conflict).
pub type MemoryDBNoMeta<H> = memory_db::MemoryDB<
	H, memory_db::HashKey<H>, trie_db::DBValue, NoMetaHasher, MemTracker,
>;
/// MemoryDB with specific meta hasher.
pub type MemoryDBMeta<H, M> = memory_db::MemoryDB<
	H, memory_db::HashKey<H>, trie_db::DBValue, M, MemTracker,
>;

/// Reexport from `hash_db`, with genericity set for `Hasher` trait.
pub type GenericMemoryDB<H, KF, MH> = memory_db::MemoryDB<
	H, KF, trie_db::DBValue, MH, MemTracker,
>;

/// Persistent trie database read-access interface for the a given hasher.
pub type TrieDB<'a, L> = trie_db::TrieDB<'a, L>;
/// Persistent trie database write-access interface for the a given hasher.
pub type TrieDBMut<'a, L> = trie_db::TrieDBMut<'a, L>;
/// Querying interface, as in `trie_db` but less generic.
pub type Lookup<'a, L, Q> = trie_db::Lookup<'a, L, Q>;
/// Hash type for a trie layout.
pub type TrieHash<L> = <<L as TrieLayout>::Hash as Hasher>::Out;
/// This module is for non generic definition of trie type.
/// Only the `Hasher` trait is generic in this case.
pub mod trie_types {
	/// State layout.
	pub type Layout<H> = super::Layout<H, super::StateHasher>;
	/// Old state layout definition, do not use meta, do not
	/// do internal value hashing.
	pub type LayoutNoMeta<H> = super::Layout<H, super::NoMetaHasher>;
	/// Persistent trie database read-access interface for the a given hasher.
	pub type TrieDB<'a, H> = super::TrieDB<'a, Layout<H>>;
	/// Persistent trie database write-access interface for the a given hasher.
	pub type TrieDBMut<'a, H> = super::TrieDBMut<'a, Layout<H>>;
	/// Persistent trie database write-access interface for the a given hasher,
	/// old layout.
	pub type TrieDBMutNoMeta<'a, H> = super::TrieDBMut<'a, LayoutNoMeta<H>>;
	/// Querying interface, as in `trie_db` but less generic.
	pub type Lookup<'a, H, Q> = trie_db::Lookup<'a, Layout<H>, Q>;
	/// As in `trie_db`, but less generic, error type for the crate.
	pub type TrieError<H> = trie_db::TrieError<H, super::Error>;
}

/// Determine a trie root given a hash DB and delta values.
pub fn delta_trie_root<L: TrieConfiguration, I, A, B, DB, V>(
	db: &mut DB,
	mut root: TrieHash<L>,
	delta: I,
	layout: L,
) -> Result<TrieHash<L>, Box<TrieError<L>>> where
	I: IntoIterator<Item = (A, B)>,
	A: Borrow<[u8]>,
	B: Borrow<Option<V>>,
	V: Borrow<[u8]>,
	DB: hash_db::HashDB<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	{
		let mut trie = TrieDBMut::<L>::from_existing_with_layout(db, &mut root, layout)?;

		let mut delta = delta.into_iter().collect::<Vec<_>>();
		delta.sort_by(|l, r| l.0.borrow().cmp(r.0.borrow()));

		for (key, change) in delta {
			match change.borrow() {
				Some(val) => trie.insert(key.borrow(), val.borrow())?,
				None => trie.remove(key.borrow())?,
			};
		}
	}

	Ok(root)
}

/// Resolve if inner hashing of value is active.
pub fn state_hashed_value<L: TrieConfiguration, DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>>(
	db: &DB,
	root: &TrieHash<L>,
) -> Option<GlobalMeta<L>> {
	struct ReadMeta<L: TrieConfiguration> {
		hashed: Option<GlobalMeta<L>>,
	}
	impl<L: TrieConfiguration> trie_db::Query<L::Hash, L::Meta> for &mut ReadMeta<L> {
		type Item = DBValue;
		fn decode(self, value: &[u8]) -> DBValue { value.to_vec() }
		fn record(&mut self, _hash: &<L::Hash as Hasher>::Out, _data: &[u8], _depth: u32, meta: &L::Meta) {
			debug_assert!(self.hashed.is_none());
			self.hashed = Some(meta.extract_global_meta());
		}
	}
	let mut read_meta: ReadMeta<L> = ReadMeta {
		hashed: None,
	};
	if let Ok(t) = TrieDB::<L>::new(&*db, root) {
		let _ = t.get_with(&[], &mut read_meta);
	}
	read_meta.hashed
}

/// Read a value from the trie.
pub fn read_trie_value<L: TrieConfiguration, DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>>(
	db: &DB,
	root: &TrieHash<L>,
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> {
	Ok(TrieDB::<L>::new(&*db, root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the trie with given Query.
pub fn read_trie_value_with<
	L: TrieConfiguration,
	Q: Query<L::Hash, L::Meta, Item=DBValue>,
	DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>
>(
	db: &DB,
	root: &TrieHash<L>,
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> {
	Ok(TrieDB::<L>::new(&*db, root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

/// Determine the empty trie root.
pub fn empty_trie_root<L: TrieConfiguration>() -> <L::Hash as Hasher>::Out {
	L::default().trie_root::<_, Vec<u8>, Vec<u8>>(core::iter::empty())
}

/// Determine the empty child trie root.
pub fn empty_child_trie_root<L: TrieConfiguration>() -> <L::Hash as Hasher>::Out {
	L::default().trie_root::<_, Vec<u8>, Vec<u8>>(core::iter::empty())
}

/// Determine a child trie root given its ordered contents, closed form. H is the default hasher,
/// but a generic implementation may ignore this type parameter and use other hashers.
pub fn child_trie_root<L: TrieConfiguration, I, A, B>(
	layout: &L,
	input: I,
) -> <L::Hash as Hasher>::Out
	where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
{
	layout.trie_root(input)
}

/// Determine a child trie root given a hash DB and delta values. H is the default hasher,
/// but a generic implementation may ignore this type parameter and use other hashers.
pub fn child_delta_trie_root<L: TrieConfiguration, I, A, B, DB, RD, V>(
	keyspace: &[u8],
	db: &mut DB,
	root_data: RD,
	delta: I,
	layout: L,
) -> Result<<L::Hash as Hasher>::Out, Box<TrieError<L>>>
	where
		I: IntoIterator<Item = (A, B)>,
		A: Borrow<[u8]>,
		B: Borrow<Option<V>>,
		V: Borrow<[u8]>,
		RD: AsRef<[u8]>,
		DB: hash_db::HashDB<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	let mut root = TrieHash::<L>::default();
	// root is fetched from DB, not writable by runtime, so it's always valid.
	root.as_mut().copy_from_slice(root_data.as_ref());

	let mut db = KeySpacedDBMut::new(&mut *db, keyspace);
	delta_trie_root::<L, _, _, _, _, _>(
		&mut db,
		root,
		delta,
		layout,
	)
}

/// Call `f` for all keys in a child trie.
/// Aborts as soon as `f` returns false.
pub fn for_keys_in_child_trie<L: TrieConfiguration, F: FnMut(&[u8]) -> bool, DB>(
	keyspace: &[u8],
	db: &DB,
	root_slice: &[u8],
	mut f: F
) -> Result<(), Box<TrieError<L>>>
	where
		DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	let mut root = TrieHash::<L>::default();
	// root is fetched from DB, not writable by runtime, so it's always valid.
	root.as_mut().copy_from_slice(root_slice);

	let db = KeySpacedDB::new(&*db, keyspace);
	let trie = TrieDB::<L>::new(&db, &root)?;
	let iter = trie.iter()?;

	for x in iter {
		let (key, _) = x?;
		if !f(&key) {
			break;
		}
	}

	Ok(())
}

/// Record all keys for a given root.
pub fn record_all_keys<L: TrieConfiguration, DB>(
	db: &DB,
	root: &TrieHash<L>,
	recorder: &mut Recorder<TrieHash<L>, L::Meta>
) -> Result<(), Box<TrieError<L>>> where
	DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	let trie = TrieDB::<L>::new(&*db, root)?;
	let iter = trie.iter()?;

	for x in iter {
		let (key, _) = x?;

		// there's currently no API like iter_with()
		// => use iter to enumerate all keys AND lookup each
		// key using get_with
		trie.get_with(&key, &mut *recorder)?;
	}

	Ok(())
}

/// Read a value from the child trie.
pub fn read_child_trie_value<L: TrieConfiguration, DB>(
	keyspace: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>>
	where
		DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	let mut root = TrieHash::<L>::default();
	// root is fetched from DB, not writable by runtime, so it's always valid.
	root.as_mut().copy_from_slice(root_slice);

	let db = KeySpacedDB::new(&*db, keyspace);
	Ok(TrieDB::<L>::new(&db, &root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the child trie with given query.
pub fn read_child_trie_value_with<L: TrieConfiguration, Q: Query<L::Hash, L::Meta, Item=DBValue>, DB>(
	keyspace: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>>
	where
		DB: hash_db::HashDBRef<L::Hash, trie_db::DBValue, L::Meta, GlobalMeta<L>>,
{
	let mut root = TrieHash::<L>::default();
	// root is fetched from DB, not writable by runtime, so it's always valid.
	root.as_mut().copy_from_slice(root_slice);

	let db = KeySpacedDB::new(&*db, keyspace);
	Ok(TrieDB::<L>::new(&db, &root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

/// `HashDB` implementation that append a encoded prefix (unique id bytes) in addition to the
/// prefix of every key value.
pub struct KeySpacedDB<'a, DB, H>(&'a DB, &'a [u8], PhantomData<H>);

/// `HashDBMut` implementation that append a encoded prefix (unique id bytes) in addition to the
/// prefix of every key value.
///
/// Mutable variant of `KeySpacedDB`, see [`KeySpacedDB`].
pub struct KeySpacedDBMut<'a, DB, H>(&'a mut DB, &'a [u8], PhantomData<H>);

/// Utility function used to merge some byte data (keyspace) and `prefix` data
/// before calling key value database primitives.
fn keyspace_as_prefix_alloc(ks: &[u8], prefix: Prefix) -> (Vec<u8>, Option<u8>) {
	let mut result = sp_std::vec![0; ks.len() + prefix.0.len()];
	result[..ks.len()].copy_from_slice(ks);
	result[ks.len()..].copy_from_slice(prefix.0);
	(result, prefix.1)
}

impl<'a, DB, H> KeySpacedDB<'a, DB, H> where
	H: Hasher,
{
	/// instantiate new keyspaced db
	pub fn new(db: &'a DB, ks: &'a [u8]) -> Self {
		KeySpacedDB(db, ks, PhantomData)
	}
}

impl<'a, DB, H> KeySpacedDBMut<'a, DB, H> where
	H: Hasher,
{
	/// instantiate new keyspaced db
	pub fn new(db: &'a mut DB, ks: &'a [u8]) -> Self {
		KeySpacedDBMut(db, ks, PhantomData)
	}
}

impl<'a, DB, H, T, M, GM> hash_db::HashDBRef<H, T, M, GM> for KeySpacedDB<'a, DB, H> where
	DB: hash_db::HashDBRef<H, T, M, GM>,
	H: Hasher,
	T: From<&'static [u8]>,
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<T> {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.get(key, (&derived_prefix.0, derived_prefix.1))
	}

	fn access_from(&self, key: &H::Out, at: Option<&H::Out>) -> Option<T> {
		self.0.access_from(key, at)
	}

	fn get_with_meta(&self, key: &H::Out, prefix: Prefix, global: GM) -> Option<(T, M)> {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.get_with_meta(key, (&derived_prefix.0, derived_prefix.1), global)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.contains(key, (&derived_prefix.0, derived_prefix.1))
	}
}

impl<'a, DB, H, T, M, GM> hash_db::HashDB<H, T, M, GM> for KeySpacedDBMut<'a, DB, H> where
	DB: hash_db::HashDB<H, T, M, GM>,
	H: Hasher,
	T: Default + PartialEq<T> + for<'b> From<&'b [u8]> + Clone + Send + Sync,
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<T> {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.get(key, (&derived_prefix.0, derived_prefix.1))
	}

	fn access_from(&self, key: &H::Out, at: Option<&H::Out>) -> Option<T> {
		self.0.access_from(key, at)
	}

	fn get_with_meta(&self, key: &H::Out, prefix: Prefix, global: GM) -> Option<(T, M)> {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.get_with_meta(key, (&derived_prefix.0, derived_prefix.1), global)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.contains(key, (&derived_prefix.0, derived_prefix.1))
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.insert((&derived_prefix.0, derived_prefix.1), value)
	}

	fn insert_with_meta(
		&mut self,
		prefix: Prefix,
		value: &[u8],
		meta: M,
	) -> H::Out {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.insert_with_meta((&derived_prefix.0, derived_prefix.1), value, meta)
	}

	fn emplace(&mut self, key: H::Out, prefix: Prefix, value: T) {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.emplace(key, (&derived_prefix.0, derived_prefix.1), value)
	}

	fn remove(&mut self, key: &H::Out, prefix: Prefix) {
		let derived_prefix = keyspace_as_prefix_alloc(self.1, prefix);
		self.0.remove(key, (&derived_prefix.0, derived_prefix.1))
	}
}

impl<'a, DB, H, T, M, GM> hash_db::AsHashDB<H, T, M, GM> for KeySpacedDBMut<'a, DB, H> where
	DB: hash_db::HashDB<H, T, M, GM>,
	H: Hasher,
	T: Default + PartialEq<T> + for<'b> From<&'b [u8]> + Clone + Send + Sync,
{
	fn as_hash_db(&self) -> &dyn hash_db::HashDB<H, T, M, GM> { &*self }

	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::HashDB<H, T, M, GM> + 'b) {
		&mut *self
	}
}

/// Representation of node with with inner hash instead of value.
fn inner_hashed_value<H: Hasher>(x: &[u8], range: Option<(usize, usize)>) -> Vec<u8> {
	if let Some((start, end)) = range {
		let len = x.len();
		if start < len && end == len {
			// terminal inner hash
			let hash_end = H::hash(&x[start..]);
			let mut buff = vec![0; x.len() + hash_end.as_ref().len() - (end - start)];
			buff[..start].copy_from_slice(&x[..start]);
			buff[start..].copy_from_slice(hash_end.as_ref());
			return buff;
		}
		if start == 0 && end < len {
			// start inner hash
			let hash_start = H::hash(&x[..start]);
			let hash_len = hash_start.as_ref().len();
			let mut buff = vec![0; x.len() + hash_len - (end - start)];
			buff[..hash_len].copy_from_slice(hash_start.as_ref());
			buff[hash_len..].copy_from_slice(&x[end..]);
			return buff;
		}
		if start < len && end < len {
			// middle inner hash
			let hash_middle = H::hash(&x[start..end]);
			let hash_len = hash_middle.as_ref().len();
			let mut buff = vec![0; x.len() + hash_len - (end - start)];
			buff[..start].copy_from_slice(&x[..start]);
			buff[start..start + hash_len].copy_from_slice(hash_middle.as_ref());
			buff[start + hash_len..].copy_from_slice(&x[end..]);
			return buff;
		}
	}
	// if anything wrong default to hash
	x.to_vec()
}

/// Estimate encoded size of node.
pub fn estimate_entry_size(entry: &(DBValue, TrieMeta), hash_len: usize) -> usize {
	use codec::Encode;
	let mut full_encoded = entry.0.encoded_size();
	if entry.1.unused_value {
		if let Some(range) = entry.1.range.as_ref() {
			let value_size = range.end - range.start;
			if range.end - range.start >= trie_constants::INNER_HASH_TRESHOLD {
				full_encoded -= value_size;
				full_encoded += hash_len;
				full_encoded += 1;
			}
		}
	}

	full_encoded
}

/// If needed, call to decode plan in order to update meta earlier.
/// TODO if removing fully meta, this will still be needed but with
/// a less generic name: read variant of node from db value and indicate
/// if can hash value.
pub fn resolve_encoded_meta<H: Hasher>(entry: &mut (DBValue, TrieMeta)) {
	use trie_db::NodeCodec;
	if entry.1.do_value_hash {
		let _ = <trie_types::Layout::<H> as TrieLayout>::Codec::decode_plan(entry.0.as_slice(), &mut entry.1);
	}
}

/// Constants used into trie simplification codec.
mod trie_constants {
	/// Treshold for using hash of value instead of value
	/// in encoded trie node when flagged.
	/// TODO design would be to make it the global meta, but then
	/// when serializing proof we would need to attach it (no way to
	/// hash the nodes otherwhise), which would
	/// break proof format.
	/// TODO attaching to storage proof in a compatible way could be
	/// achieve by using a escaped header in first or last element of proof
	/// and write it after.
	pub const INNER_HASH_TRESHOLD: usize = 33;
	const FIRST_PREFIX: u8 = 0b_00 << 6;
	/// In proof this header is used when only hashed value is stored.
	pub const DEAD_HEADER_META_HASHED_VALUE: u8 = EMPTY_TRIE | 0b_00_01;
	pub const NIBBLE_SIZE_BOUND: usize = u16::max_value() as usize;
	pub const LEAF_PREFIX_MASK: u8 = 0b_01 << 6;
	pub const BRANCH_WITHOUT_MASK: u8 = 0b_10 << 6;
	pub const BRANCH_WITH_MASK: u8 = 0b_11 << 6;
	pub const EMPTY_TRIE: u8 = FIRST_PREFIX | (0b_00 << 4);
	pub const ALT_HASHING_LEAF_PREFIX_MASK: u8 = FIRST_PREFIX | (0b_01 << 4);
	pub const ALT_HASHING_BRANCH_WITHOUT_MASK: u8 = FIRST_PREFIX | (0b_10 << 4);
	pub const ALT_HASHING_BRANCH_WITH_MASK: u8 = FIRST_PREFIX | (0b_11 << 4);
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Decode, Compact};
	use sp_core::Blake2Hasher;
	use hash_db::{HashDB, Hasher};
	use trie_db::{DBValue, TrieMut, Trie, NodeCodec as NodeCodecT};
	use trie_standardmap::{Alphabet, ValueMode, StandardMap};
	use hex_literal::hex;

	type Layout = super::trie_types::Layout<Blake2Hasher>;

	fn hashed_null_node<T: TrieConfiguration>() -> TrieHash<T> {
		<T::Codec as NodeCodecT<T::Meta>>::hashed_null_node()
	}

	fn check_equivalent<T: TrieConfiguration>(input: &Vec<(&[u8], &[u8])>, layout: T) {
		{
			let closed_form = layout.trie_root(input.clone());
			let d = layout.trie_root_unhashed(input.clone());
			println!("Data: {:#x?}, {:#x?}", d, Blake2Hasher::hash(&d[..]));
			let persistent = {
				let mut memdb = MemoryDBMeta::<_, T::MetaHasher>::default();
				let mut root = Default::default();
				let mut t = TrieDBMut::<T>::new_with_layout(&mut memdb, &mut root, layout);
				for (x, y) in input.iter().rev() {
					t.insert(x, y).unwrap();
				}
				t.root().clone()
			};
			assert_eq!(closed_form, persistent);
		}
	}

	fn check_iteration<T: TrieConfiguration>(input: &Vec<(&[u8], &[u8])>, layout: T) {
		let mut memdb = MemoryDBMeta::<_, T::MetaHasher>::default();
		let mut root = Default::default();
		{
			let mut t = TrieDBMut::<T>::new_with_layout(&mut memdb, &mut root, layout);
			for (x, y) in input.clone() {
				t.insert(x, y).unwrap();
			}
		}
		{
			// Not using layout: it should be initialized from state root meta.
			let t = TrieDB::<T>::new(&mut memdb, &root).unwrap();
			assert_eq!(
				input.iter().map(|(i, j)| (i.to_vec(), j.to_vec())).collect::<Vec<_>>(),
				t.iter().unwrap()
					.map(|x| x.map(|y| (y.0, y.1.to_vec())).unwrap())
					.collect::<Vec<_>>()
			);
		}
	}

	fn check_input(input: &Vec<(&[u8], &[u8])>) {
// TODO remove this iter
		let layout = Layout::with_inner_hashing();
		check_equivalent::<Layout>(input, layout.clone());


		let layout = Layout::default();
		check_equivalent::<Layout>(input, layout.clone());
		check_iteration::<Layout>(input, layout);
		let layout = Layout::with_inner_hashing();
		check_equivalent::<Layout>(input, layout.clone());
		check_iteration::<Layout>(input, layout);
	}

	#[test]
	fn default_trie_root() {
		let mut db = MemoryDB::default();
		let mut root = TrieHash::<Layout>::default();
		let mut empty = TrieDBMut::<Layout>::new(&mut db, &mut root);
		empty.commit();
		let root1 = empty.root().as_ref().to_vec();
		let root2: Vec<u8> = Layout::default().trie_root::<_, Vec<u8>, Vec<u8>>(
			std::iter::empty(),
		).as_ref().iter().cloned().collect();

		assert_eq!(root1, root2);
	}

	#[test]
	fn empty_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![];
		check_input(&input);
	}

	#[test]
	fn leaf_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0xbb][..])];
		check_input(&input);
	}

	#[test]
	fn branch_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0x10][..]),
			(&[0xba][..], &[0x11][..]),
		];
		check_input(&input);
	}

	#[test]
	fn extension_and_branch_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0x10][..]),
			(&[0xab][..], &[0x11][..]),
		];
		check_input(&input);
	}

	#[test]
	fn standard_is_equivalent() {
		let st = StandardMap {
			alphabet: Alphabet::All,
			min_key: 32,
			journal_key: 0,
			value_mode: ValueMode::Random,
			count: 1000,
		};
		let mut d = st.make();
		d.sort_by(|&(ref a, _), &(ref b, _)| a.cmp(b));
		let dr = d.iter().map(|v| (&v.0[..], &v.1[..])).collect();
		check_input(&dr);
	}

	#[test]
	fn extension_and_branch_with_value_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0xa0][..]),
			(&[0xaa, 0xaa][..], &[0xaa][..]),
			(&[0xaa, 0xbb][..], &[0xab][..])
		];
		check_input(&input);
	}

	#[test]
	fn bigger_extension_and_branch_with_value_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0xa0][..]),
			(&[0xaa, 0xaa][..], &[0xaa][..]),
			(&[0xaa, 0xbb][..], &[0xab][..]),
			(&[0xbb][..], &[0xb0][..]),
			(&[0xbb, 0xbb][..], &[0xbb][..]),
			(&[0xbb, 0xcc][..], &[0xbc][..]),
		];
		check_input(&input);
	}

	#[test]
	fn single_long_leaf_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]),
			(&[0xba][..], &[0x11][..]),
		];
		check_input(&input);
	}

	#[test]
	fn two_long_leaves_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]),
			(&[0xba][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..])
		];
		check_input(&input);
	}

	fn populate_trie<'db, T>(
		db: &'db mut dyn HashDB<T::Hash, DBValue, T::Meta, GlobalMeta<T>>,
		root: &'db mut TrieHash<T>,
		v: &[(Vec<u8>, Vec<u8>)],
		layout: T,
	) -> TrieDBMut<'db, T>
		where
			T: TrieConfiguration<Meta = TrieMeta>,
	{
		let mut t = TrieDBMut::<T>::new_with_layout(db, root, layout);
		for i in 0..v.len() {
			let key: &[u8]= &v[i].0;
			let val: &[u8] = &v[i].1;
			t.insert(key, val).unwrap();
		}
		t
	}

	fn unpopulate_trie<'db, T: TrieConfiguration>(
		t: &mut TrieDBMut<'db, T>,
		v: &[(Vec<u8>, Vec<u8>)],
	) {
		for i in v {
			let key: &[u8]= &i.0;
			t.remove(key).unwrap();
		}
	}

	#[test]
	fn random_should_work() {
		random_should_work_inner(true);
		random_should_work_inner(false);
	}
	fn random_should_work_inner(flag: bool) {
		let mut seed = <Blake2Hasher as Hasher>::Out::zero();
		for test_i in 0..10_000 {
			if test_i % 50 == 0 {
				println!("{:?} of 10000 stress tests done", test_i);
			}
			let x = StandardMap {
				alphabet: Alphabet::Custom(b"@QWERTYUIOPASDFGHJKLZXCVBNM[/]^_".to_vec()),
				min_key: 5,
				journal_key: 0,
				value_mode: ValueMode::Index,
				count: 100,
			}.make_with(seed.as_fixed_bytes_mut());

			let layout = if flag {
				Layout::with_inner_hashing()
			} else {
				Layout::default()
			};
			let real = layout.trie_root(x.clone());
			let mut memdb = MemoryDB::default();
			let mut root = Default::default();

			let mut memtrie = populate_trie::<Layout>(&mut memdb, &mut root, &x, layout.clone());

			memtrie.commit();
			if *memtrie.root() != real {
				println!("TRIE MISMATCH");
				println!("");
				println!("{:?} vs {:?}", memtrie.root(), real);
				for i in &x {
					println!("{:#x?} -> {:#x?}", i.0, i.1);
				}
			}
			assert_eq!(*memtrie.root(), real);
			unpopulate_trie::<Layout>(&mut memtrie, &x);
			memtrie.commit();
			let hashed_null_node = hashed_null_node::<Layout>();
			if *memtrie.root() != hashed_null_node {
				println!("- TRIE MISMATCH");
				println!("");
				println!("{:?} vs {:?}", memtrie.root(), hashed_null_node);
				for i in &x {
					println!("{:#x?} -> {:#x?}", i.0, i.1);
				}
			}
			assert_eq!(*memtrie.root(), hashed_null_node);
		}
	}

	fn to_compact(n: u8) -> u8 {
		Compact(n).encode()[0]
	}

	#[test]
	fn codec_trie_empty() {
		let layout = Layout::default();
		let input: Vec<(&[u8], &[u8])> = vec![];
		let trie = layout.trie_root_unhashed(input);
		println!("trie: {:#x?}", trie);
		assert_eq!(trie, vec![0x0]);
	}

	#[test]
	fn codec_trie_single_tuple() {
		let layout = Layout::default();
		let input = vec![
			(vec![0xaa], vec![0xbb])
		];
		let trie = layout.trie_root_unhashed(input);
		println!("trie: {:#x?}", trie);
		assert_eq!(trie, vec![
			0x42,					// leaf 0x40 (2^6) with (+) key of 2 nibbles (0x02)
			0xaa,					// key data
			to_compact(1),			// length of value in bytes as Compact
			0xbb					// value data
		]);
	}

	#[test]
	fn codec_trie_two_tuples_disjoint_keys() {
		let layout = Layout::default();
		let input = vec![(&[0x48, 0x19], &[0xfe]), (&[0x13, 0x14], &[0xff])];
		let trie = layout.trie_root_unhashed(input);
		println!("trie: {:#x?}", trie);
		let mut ex = Vec::<u8>::new();
		ex.push(0x80);									// branch, no value (0b_10..) no nibble
		ex.push(0x12);									// slots 1 & 4 are taken from 0-7
		ex.push(0x00);									// no slots from 8-15
		ex.push(to_compact(0x05));						// first slot: LEAF, 5 bytes long.
		ex.push(0x43);									// leaf 0x40 with 3 nibbles
		ex.push(0x03);									// first nibble
		ex.push(0x14);									// second & third nibble
		ex.push(to_compact(0x01));						// 1 byte data
		ex.push(0xff);									// value data
		ex.push(to_compact(0x05));						// second slot: LEAF, 5 bytes long.
		ex.push(0x43);									// leaf with 3 nibbles
		ex.push(0x08);									// first nibble
		ex.push(0x19);									// second & third nibble
		ex.push(to_compact(0x01));						// 1 byte data
		ex.push(0xfe);									// value data

		assert_eq!(trie, ex);
	}

	#[test]
	fn iterator_works() {
		iterator_works_inner(true);
		iterator_works_inner(false);
	}
	fn iterator_works_inner(flag: bool) {
		let layout = if flag {
			Layout::with_inner_hashing()
		} else {
			Layout::default()
		};

		let pairs = vec![
			(hex!("0103000000000000000464").to_vec(), hex!("0400000000").to_vec()),
			(hex!("0103000000000000000469").to_vec(), hex!("0401000000").to_vec()),
		];

		let mut mdb = MemoryDB::default();
		let mut root = Default::default();
		let _ = populate_trie::<Layout>(&mut mdb, &mut root, &pairs, layout.clone());

		let trie = TrieDB::<Layout>::new_with_layout(&mdb, &root, layout).unwrap();

		let iter = trie.iter().unwrap();
		let mut iter_pairs = Vec::new();
		for pair in iter {
			let (key, value) = pair.unwrap();
			iter_pairs.push((key, value.to_vec()));
		}

		assert_eq!(pairs, iter_pairs);
	}

	#[test]
	fn generate_storage_root_with_proof_works_independently_from_the_delta_order() {
		let proof = StorageProof::decode(&mut &include_bytes!("../test-res/proof")[..]).unwrap();
		let storage_root = sp_core::H256::decode(
			&mut &include_bytes!("../test-res/storage_root")[..],
		).unwrap();
		// Delta order that is "invalid" so that it would require a different proof.
		let invalid_delta = Vec::<(Vec<u8>, Option<Vec<u8>>)>::decode(
			&mut &include_bytes!("../test-res/invalid-delta-order")[..],
		).unwrap();
		// Delta order that is "valid"
		let valid_delta = Vec::<(Vec<u8>, Option<Vec<u8>>)>::decode(
			&mut &include_bytes!("../test-res/valid-delta-order")[..],
		).unwrap();

		let proof_db = proof.into_memory_db::<Blake2Hasher>();
		let first_storage_root = delta_trie_root::<Layout, _, _, _, _, _>(
			&mut proof_db.clone(),
			storage_root,
			valid_delta,
			Default::default(),
		).unwrap();
		let second_storage_root = delta_trie_root::<Layout, _, _, _, _, _>(
			&mut proof_db.clone(),
			storage_root,
			invalid_delta,
			Default::default(),
		).unwrap();

		assert_eq!(first_storage_root, second_storage_root);
	}
}
