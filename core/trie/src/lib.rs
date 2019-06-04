// Copyright 2015-2019 Parity Technologies (UK) Ltd.
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

//! Utility functions to interact with Substrate's Base-16 Modified Merkle Patricia tree ("trie").

#![cfg_attr(not(feature = "std"), no_std)]

mod error;
mod node_header;
mod node_codec;
mod trie_stream;
mod legacy;

use rstd::boxed::Box;
use rstd::vec::Vec;
use hash_db::Hasher;
/// Our `NodeCodec`-specific error.
pub use error::Error;
/// The Substrate format implementation of `TrieStream`.
pub use trie_stream::TrieStream;
/// Legacy format implementation of `TrieStream`.
pub use legacy::trie_stream::TrieStream as LegacyTrieStream;
/// The Substrate format implementation of `NodeCodec`.
pub use node_codec::NodeCodec;
/// Legacy format implementation of `NodeCodec`.
pub use legacy::node_codec::NodeCodec as LegacyNodeCodec;
/// Various re-exports from the `trie-db` crate.
pub use trie_db::{Trie, TrieMut, DBValue, Recorder, CError,
	Query, TrieLayOut, TrieOps, NibbleHalf, Cache16, NibbleOps};
/// Various re-exports from the `memory-db` crate.
pub use memory_db::{KeyFunction, prefixed_key};


#[derive(Default)]
/// substrate trie layout
pub struct Layout<H>(rstd::marker::PhantomData<H>);

impl<H: Hasher> TrieLayOut for Layout<H> {
	const USE_EXTENSION: bool = false;
	type H = H;
	type C = NodeCodec<Self::H, Self::N, node_codec::BitMap16>;
	type N = NibbleHalf;
	type CB = Cache16;
}

impl<H: Hasher> TrieOps for Layout<H> {
	fn trie_root<I, A, B>(input: I) -> <Self::H as Hasher>::Out where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	{
		trie_root::trie_root_no_ext::<H, TrieStream, _, _, _>(input)
	}
	
	fn trie_root_unhashed<I, A, B>(input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	{
		trie_root::unhashed_trie_no_ext::<H, TrieStream, _, _, _>(input)
	}
	
	fn encode_index(input: u32) -> Vec<u8> {
		codec::Encode::encode(&codec::Compact(input))
	}
}

#[derive(Default)]
/// substrate trie layout
pub struct LegacyLayout<H>(rstd::marker::PhantomData<H>);

impl<H: Hasher> TrieLayOut for LegacyLayout<H> {
	const USE_EXTENSION: bool = true;
	type H = H;
	type C = LegacyNodeCodec<Self::H, Self::N, node_codec::BitMap16>;
	type N = NibbleHalf;
	type CB = Cache16;
}

impl<H: Hasher> TrieOps for LegacyLayout<H> {
	fn trie_root<I, A, B>(input: I) -> <Self::H as Hasher>::Out where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	{
		trie_root::trie_root::<H, LegacyTrieStream, _, _, _>(input)
	}
	
	fn trie_root_unhashed<I, A, B>(input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	{
		trie_root::unhashed_trie::<H, LegacyTrieStream, _, _, _>(input)
	}
	
	fn encode_index(input: u32) -> Vec<u8> {
		codec::Encode::encode(&codec::Compact(input))
	}
}


/// `trie_db`, error type.
pub type TrieError<L> = trie_db::TrieError<TrieHash<L>, CError<L>>;
/// As in `hash_db`, but less generic, trait exposed.
pub trait AsHashDB<H: Hasher>: hash_db::AsHashDB<H, trie_db::DBValue> {}
impl<H: Hasher, T: hash_db::AsHashDB<H, trie_db::DBValue>> AsHashDB<H> for T {}
/// As in `hash_db`, but less generic, trait exposed.
pub type HashDB<'a, H> = hash_db::HashDB<H, trie_db::DBValue> + 'a;
/// As in `hash_db`, but less generic, trait exposed.
pub type PlainDB<'a, K> = hash_db::PlainDB<K, trie_db::DBValue> + 'a;
/// As in `memory_db::MemoryDB` that uses prefixed storage key scheme.
pub type PrefixedMemoryDB<H> = memory_db::MemoryDB<H, memory_db::PrefixedKey<H>, trie_db::DBValue>;
/// As in `memory_db::MemoryDB` that uses prefixed storage key scheme.
pub type MemoryDB<H> = memory_db::MemoryDB<H, memory_db::HashKey<H>, trie_db::DBValue>;
/// As in `memory_db`, but less generic, trait exposed.
pub type GenericMemoryDB<H, KF> = memory_db::MemoryDB<H, KF, trie_db::DBValue>;

/// Persistent trie database read-access interface for the a given hasher.
pub type TrieDB<'a, L> = trie_db::TrieDB<'a, L>;
/// Persistent trie database write-access interface for the a given hasher.
pub type TrieDBMut<'a, L> = trie_db::TrieDBMut<'a, L>;
/// Querying interface, as in `trie_db` but less generic.
pub type Lookup<'a, L, Q> = trie_db::Lookup<'a, L, Q>;
/// Hash type for a trie layout.
pub type TrieHash<L> = <<L as TrieLayOut>::H as Hasher>::Out;

/// This module is for non generic definition of trie type.
/// Only the `Hasher` is generic in this case.
pub mod trie_types {
	pub type LayOut<H> = super::Layout<H>;
	/// Persistent trie database read-access interface for the a given hasher.
	pub type TrieDB<'a, H> = super::TrieDB<'a, LayOut<H>>;
	/// Persistent trie database write-access interface for the a given hasher.
	pub type TrieDBMut<'a, H> = super::TrieDBMut<'a, LayOut<H>>;
	/// Querying interface, as in `trie_db` but less generic.
	pub type Lookup<'a, H, Q> = trie_db::Lookup<'a, LayOut<H>, Q>;
	/// As in `trie_db`, but less generic, error type for the crate.
	pub type TrieError<H> = trie_db::TrieError<H, super::Error>;
}

/// Determine a trie root given a hash DB and delta values.
pub fn delta_trie_root<L: TrieOps, I, A, B, DB>(
	db: &mut DB,
	mut root: TrieHash<L>,
	delta: I
) -> Result<TrieHash<L>, Box<TrieError<L>>> where
	I: IntoIterator<Item = (A, Option<B>)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	DB: hash_db::HashDB<L::H, trie_db::DBValue>,
{
	{
		let mut trie = TrieDBMut::<L>::from_existing(&mut *db, &mut root)?;

		for (key, change) in delta {
			match change {
				Some(val) => trie.insert(key.as_ref(), val.as_ref())?,
				None => trie.remove(key.as_ref())?,
			};
		}
	}

	Ok(root)
}

/// Read a value from the trie.
pub fn read_trie_value<L: TrieOps, DB: hash_db::HashDBRef<L::H, trie_db::DBValue>>(
	db: &DB,
	root: &TrieHash<L>,
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> {
	Ok(TrieDB::<L>::new(&*db, root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the trie with given Query.
pub fn read_trie_value_with<L: TrieOps, Q: Query<L::H, Item=DBValue>, DB: hash_db::HashDBRef<L::H, trie_db::DBValue>>(
	db: &DB,
	root: &TrieHash<L>,
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> {
	Ok(TrieDB::<L>::new(&*db, root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

/// Determine whether a child trie key is valid.
///
/// For now, the only valid child trie key is `:child_storage:default:`.
///
/// `child_trie_root` and `child_delta_trie_root` can panic if invalid value is provided to them.
pub fn is_child_trie_key_valid<L: TrieOps>(storage_key: &[u8]) -> bool {
	use substrate_primitives::storage::well_known_keys;
	let has_right_prefix = storage_key.starts_with(b":child_storage:default:");
	if has_right_prefix {
		// This is an attempt to catch a change of `is_child_storage_key`, which
		// just checks if the key has prefix `:child_storage:` at the moment of writing.
		debug_assert!(
			well_known_keys::is_child_storage_key(&storage_key),
			"`is_child_trie_key_valid` is a subset of `is_child_storage_key`",
		);
	}
	has_right_prefix
}

/// Determine the default child trie root.
pub fn default_child_trie_root<L: TrieOps>(_storage_key: &[u8]) -> Vec<u8> {
	L::trie_root::<_, Vec<u8>, Vec<u8>>(core::iter::empty()).as_ref().iter().cloned().collect()
}

/// Determine a child trie root given its ordered contents, closed form. H is the default hasher, but a generic
/// implementation may ignore this type parameter and use other hashers.
pub fn child_trie_root<L: TrieOps, I, A, B>(_storage_key: &[u8], input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
{
	L::trie_root(input).as_ref().iter().cloned().collect()
}

/// Determine a child trie root given a hash DB and delta values. H is the default hasher, but a generic implementation may ignore this type parameter and use other hashers.
pub fn child_delta_trie_root<L: TrieOps, I, A, B, DB>(
	_storage_key: &[u8],
	db: &mut DB,
	root_vec: Vec<u8>,
	delta: I
) -> Result<Vec<u8>, Box<TrieError<L>>> where
	I: IntoIterator<Item = (A, Option<B>)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	DB: hash_db::HashDB<L::H, trie_db::DBValue> + hash_db::PlainDB<TrieHash<L>, trie_db::DBValue>,
{
	let mut root = TrieHash::<L>::default();
	root.as_mut().copy_from_slice(&root_vec); // root is fetched from DB, not writable by runtime, so it's always valid.

	{
		let mut trie = TrieDBMut::<L>::from_existing(&mut *db, &mut root)?;

		for (key, change) in delta {
			match change {
				Some(val) => trie.insert(key.as_ref(), val.as_ref())?,
				None => trie.remove(key.as_ref())?,
			};
		}
	}

	Ok(root.as_ref().to_vec())
}

/// Call `f` for all keys in a child trie.
pub fn for_keys_in_child_trie<L: TrieOps, F: FnMut(&[u8]), DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	mut f: F
) -> Result<(), Box<TrieError<L>>> where
	DB: hash_db::HashDBRef<L::H, trie_db::DBValue> + hash_db::PlainDBRef<TrieHash<L>, trie_db::DBValue>,
{
	let mut root = TrieHash::<L>::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	let trie = TrieDB::<L>::new(&*db, &root)?;
	let iter = trie.iter()?;

	for x in iter {
		let (key, _) = x?;
		f(&key);
	}

	Ok(())
}

/// Record all keys for a given root.
pub fn record_all_keys<L: TrieOps, DB>(
	db: &DB,
	root: &TrieHash<L>,
	recorder: &mut Recorder<TrieHash<L>>
) -> Result<(), Box<TrieError<L>>> where
	DB: hash_db::HashDBRef<L::H, trie_db::DBValue>
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
pub fn read_child_trie_value<L: TrieOps, DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
	DB: hash_db::HashDBRef<L::H, trie_db::DBValue> + hash_db::PlainDBRef<TrieHash<L>, trie_db::DBValue>,
{
	let mut root = TrieHash::<L>::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	Ok(TrieDB::<L>::new(&*db, &root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the child trie with given query.
pub fn read_child_trie_value_with<L: TrieOps, Q: Query<L::H, Item=DBValue>, DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
	DB: hash_db::HashDBRef<L::H, trie_db::DBValue> + hash_db::PlainDBRef<TrieHash<L>, trie_db::DBValue>,
{
	let mut root = TrieHash::<L>::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	Ok(TrieDB::<L>::new(&*db, &root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

/// constants used with trie simplification codec
mod s_cst {
	pub const EMPTY_TRIE: u8 = 0;
	pub const NIBBLE_SIZE_BOUND: usize = u16::max_value() as usize;
	pub const LEAF_PREFIX_MASK: u8 = 0b_01 << 6;
	pub const BRANCH_WITHOUT_MASK: u8 = 0b_10 << 6;
	pub const BRANCH_WITH_MASK: u8 = 0b_11 << 6;
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Compact};
	use substrate_primitives::Blake2Hasher;
	use hash_db::{HashDB, Hasher};
	use trie_db::{DBValue, TrieMut, Trie, NodeCodec as NodeCodecT};
	use trie_standardmap::{Alphabet, ValueMode, StandardMap};
	use hex_literal::hex;

	type Layout = super::Layout<Blake2Hasher>;
	type LayoutLegagacy = super::LegacyLayout<Blake2Hasher>;

	fn hashed_null_node<T: TrieOps>() -> TrieHash<T> {
		<T::C as NodeCodecT<_, _>>::hashed_null_node()
	}

	fn check_equivalent<T: TrieOps>(input: &Vec<(&[u8], &[u8])>) {
		{
			let closed_form = T::trie_root::<_, _, _>(input.clone());
			let d = T::trie_root_unhashed::<_, _, _>(input.clone());
			println!("Data: {:#x?}, {:#x?}", d, Blake2Hasher::hash(&d[..]));
			let persistent = {
				let mut memdb = MemoryDB::default();
				let mut root = Default::default();
				let mut t = TrieDBMut::<T>::new(&mut memdb, &mut root);
				for (x, y) in input.iter().rev() {
					t.insert(x, y).unwrap();
				}
				t.root().clone()
			};
			assert_eq!(closed_form, persistent);
		}
	}

	fn check_iteration<T: TrieOps>(input: &Vec<(&[u8], &[u8])>) {
		let mut memdb = MemoryDB::default();
		let mut root = Default::default();
		{
			let mut t = TrieDBMut::<T>::new(&mut memdb, &mut root);
			for (x, y) in input.clone() {
				t.insert(x, y).unwrap();
			}
		}
		{
			let t = TrieDB::<T>::new(&mut memdb, &root).unwrap();
			assert_eq!(
				input.iter().map(|(i, j)| (i.to_vec(), j.to_vec())).collect::<Vec<_>>(),
				t.iter().unwrap().map(|x| x.map(|y| (y.0, y.1.to_vec())).unwrap()).collect::<Vec<_>>()
			);
		}
	}

	#[test]
	fn default_trie_root() {
		default_trie_root_inner::<Layout>()
	}
	#[test]
	fn default_trie_root_legacy() {
		default_trie_root_inner::<LayoutLegagacy>()
	}
	fn default_trie_root_inner<T: TrieOps>() {
		let mut db = MemoryDB::default();
		let mut root = TrieHash::<T>::default();
		let mut empty = TrieDBMut::<T>::new(&mut db, &mut root);
		empty.commit();
		let root1 = empty.root().as_ref().to_vec();
		let root2: Vec<u8> = T::trie_root::<_, Vec<u8>, Vec<u8>>(std::iter::empty()).as_ref().iter().cloned().collect();

		assert_eq!(root1, root2);
	}

	#[test]
	fn empty_is_equivalent() {
		empty_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn empty_is_equivalent_legacy() {
		empty_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn empty_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn leaf_is_equivalent() {
		leaf_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn leaf_is_equivalent_legacy() {
		leaf_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn leaf_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0xbb][..])];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn branch_is_equivalent() {
		branch_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn branch_is_equivalent_legacy() {
		branch_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn branch_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0x10][..]), (&[0xba][..], &[0x11][..])];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn extension_and_branch_is_equivalent() {
		extension_and_branch_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn extension_and_branch_is_equivalent_legacy() {
		extension_and_branch_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn extension_and_branch_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0x10][..]), (&[0xab][..], &[0x11][..])];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn standard_is_equivalent() {
		standard_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn standard_is_equivalent_legacy() {
		standard_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn standard_is_equivalent_inner<T: TrieOps>() {
		let st = StandardMap {
			alphabet: Alphabet::All,
			min_key: 32,
			journal_key: 0,
			value_mode: ValueMode::Random,
			count: 1000,
		};
		let mut d = st.make();
		d.sort_unstable_by(|&(ref a, _), &(ref b, _)| a.cmp(b));
		let dr = d.iter().map(|v| (&v.0[..], &v.1[..])).collect();
		check_equivalent::<T>(&dr);
		check_iteration::<T>(&dr);
	}

	#[test]
	fn extension_and_branch_with_value_is_equivalent() {
		extension_and_branch_with_value_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn extension_and_branch_with_value_is_equivalent_legacy() {
		extension_and_branch_with_value_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn extension_and_branch_with_value_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0xa0][..]),
			(&[0xaa, 0xaa][..], &[0xaa][..]),
			(&[0xaa, 0xbb][..], &[0xab][..])
		];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn bigger_extension_and_branch_with_value_is_equivalent() {
		bigger_extension_and_branch_with_value_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn bigger_extension_and_branch_with_value_is_equivalent_legacy() {
		bigger_extension_and_branch_with_value_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn bigger_extension_and_branch_with_value_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0xa0][..]),
			(&[0xaa, 0xaa][..], &[0xaa][..]),
			(&[0xaa, 0xbb][..], &[0xab][..]),
			(&[0xbb][..], &[0xb0][..]),
			(&[0xbb, 0xbb][..], &[0xbb][..]),
			(&[0xbb, 0xcc][..], &[0xbc][..]),
		];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn single_long_leaf_is_equivalent() {
		single_long_leaf_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn single_long_leaf_is_equivalent_legacy() {
		single_long_leaf_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn single_long_leaf_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]), (&[0xba][..], &[0x11][..])];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	#[test]
	fn two_long_leaves_is_equivalent() {
		two_long_leaves_is_equivalent_inner::<Layout>()
	}
	#[test]
	fn two_long_leaves_is_equivalent_legacy() {
		two_long_leaves_is_equivalent_inner::<LayoutLegagacy>()
	}
	fn two_long_leaves_is_equivalent_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]),
			(&[0xba][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..])
		];
		check_equivalent::<T>(&input);
		check_iteration::<T>(&input);
	}

	fn populate_trie<'db, T: TrieOps>(
		db: &'db mut HashDB<T::H, DBValue>,
		root: &'db mut TrieHash<T>,
		v: &[(Vec<u8>, Vec<u8>)]
	) -> TrieDBMut<'db, T> {
		let mut t = TrieDBMut::<T>::new(db, root);
		for i in 0..v.len() {
			let key: &[u8]= &v[i].0;
			let val: &[u8] = &v[i].1;
			t.insert(key, val).unwrap();
		}
		t
	}

	fn unpopulate_trie<'db, T: TrieOps>(t: &mut TrieDBMut<'db, T>, v: &[(Vec<u8>, Vec<u8>)]) {
		for i in v {
			let key: &[u8]= &i.0;
			t.remove(key).unwrap();
		}
	}

	#[test]
	fn random_should_work() {
		random_should_work_inner::<Layout>()
	}
	#[test]
	fn random_should_work_legacy() {
		random_should_work_inner::<LayoutLegagacy>()
	}

	fn random_should_work_inner<T: TrieOps>() {
		let mut seed = <Blake2Hasher as Hasher>::Out::zero();
		//for test_i in 0..10000 {
		for test_i in 0..1000 {
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

			let real = T::trie_root(x.clone());
			let mut memdb = MemoryDB::default();
			let mut root = Default::default();
			let mut memtrie = populate_trie::<T>(&mut memdb, &mut root, &x);

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
			unpopulate_trie::<T>(&mut memtrie, &x);
			memtrie.commit();
			let hashed_null_node = hashed_null_node::<T>();
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
		codec_trie_empty_inner::<Layout>()
	}
	#[test]
	fn codec_trie_empty_legacy() {
		codec_trie_empty_inner::<LayoutLegagacy>()
	}
	fn codec_trie_empty_inner<T: TrieOps>() {
		let input: Vec<(&[u8], &[u8])> = vec![];
		let trie = T::trie_root_unhashed::<_, _, _>(input);
		println!("trie: {:#x?}", trie);
		assert_eq!(trie, vec![0x0]);
	}

	#[test]
	fn codec_trie_single_tuple() {
		let input = vec![
			(vec![0xaa], vec![0xbb])
		];
		let trie = Layout::trie_root_unhashed::<_, _, _>(input);
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
		let input = vec![(&[0x48, 0x19], &[0xfe]), (&[0x13, 0x14], &[0xff])];
		let trie = Layout::trie_root_unhashed::<_, _, _>(input);
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
		iterator_works_inner::<Layout>()
	}
	#[test]
	fn iterator_works_legacy() {
		iterator_works_inner::<LayoutLegagacy>()
	}
	fn iterator_works_inner<T: TrieOps>() {
		let pairs = vec![
			(hex!("0103000000000000000464").to_vec(), hex!("0400000000").to_vec()),
			(hex!("0103000000000000000469").to_vec(), hex!("0401000000").to_vec()),
		];

		let mut mdb = MemoryDB::default();
		let mut root = Default::default();
		let _ = populate_trie::<T>(&mut mdb, &mut root, &pairs);

		let trie = TrieDB::<T>::new(&mdb, &root).unwrap();

		let iter = trie.iter().unwrap();
		let mut iter_pairs = Vec::new();
		for pair in iter {
			let (key, value) = pair.unwrap();
			iter_pairs.push((key, value.to_vec()));
		}

		assert_eq!(pairs, iter_pairs);
	}
}
