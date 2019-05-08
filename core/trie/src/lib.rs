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

use rstd::boxed::Box;
use rstd::vec::Vec;
use hash_db::Hasher;
/// Our `NodeCodec`-specific error.
pub use error::Error;
/// The Substrate format implementation of `TrieStream`.
pub use trie_stream::TrieStream;
/// The Substrate format implementation of `NodeCodec`.
pub use node_codec::NodeCodec;
/// Various re-exports from the `trie-db` crate.
pub use trie_db::{Trie, TrieMut, DBValue, Recorder, Query};
/// Various re-exports from the `memory-db` crate.
pub use memory_db::{KeyFunction, prefixed_key};

/// As in `trie_db`, but less generic, error type for the crate.
pub type TrieError<H> = trie_db::TrieError<H, Error>;
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
pub type TrieDB<'a, H> = trie_db::TrieDB<'a, H, NodeCodec<H>>;
/// Persistent trie database write-access interface for the a given hasher.
pub type TrieDBMut<'a, H> = trie_db::TrieDBMut<'a, H, NodeCodec<H>>;
/// Querying interface, as in `trie_db` but less generic.
pub type Lookup<'a, H, Q> = trie_db::Lookup<'a, H, NodeCodec<H>, Q>;

/// Determine a trie root given its ordered contents, closed form.
pub fn trie_root<H: Hasher, I, A, B>(input: I) -> H::Out where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
{
	trie_root::trie_root::<H, TrieStream, _, _, _>(input)
}

/// Determine a trie root given a hash DB and delta values.
pub fn delta_trie_root<H: Hasher, I, A, B, DB>(
	db: &mut DB,
	mut root: H::Out,
	delta: I
) -> Result<H::Out, Box<TrieError<H::Out>>> where
	I: IntoIterator<Item = (A, Option<B>)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	DB: hash_db::HashDB<H, trie_db::DBValue>,
{
	{
		let mut trie = TrieDBMut::<H>::from_existing(&mut *db, &mut root)?;

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
pub fn read_trie_value<H: Hasher, DB: hash_db::HashDBRef<H, trie_db::DBValue>>(
	db: &DB,
	root: &H::Out,
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<H::Out>>> {
	Ok(TrieDB::<H>::new(&*db, root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the trie with given Query.
pub fn read_trie_value_with<H: Hasher, Q: Query<H, Item=DBValue>, DB: hash_db::HashDBRef<H, trie_db::DBValue>>(
	db: &DB,
	root: &H::Out,
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<H::Out>>> {
	Ok(TrieDB::<H>::new(&*db, root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

/// Determine a trie root node's data given its ordered contents, closed form.
pub fn unhashed_trie<H: Hasher, I, A, B>(input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
{
	trie_root::unhashed_trie::<H, TrieStream, _, _, _>(input)
}

/// A trie root formed from the items, with keys attached according to their
/// compact-encoded index (using `parity-codec` crate).
pub fn ordered_trie_root<H: Hasher, I, A>(input: I) -> H::Out
where
	I: IntoIterator<Item = A>,
	A: AsRef<[u8]>,
{
	trie_root::<H, _, _, _>(input
		.into_iter()
		.enumerate()
		.map(|(i, v)| (codec::Encode::encode(&codec::Compact(i as u32)), v))
	)
}

/// Determine whether a child trie key is valid.
///
/// For now, the only valid child trie key is `:child_storage:default:`.
///
/// `child_trie_root` and `child_delta_trie_root` can panic if invalid value is provided to them.
pub fn is_child_trie_key_valid<H: Hasher>(storage_key: &[u8]) -> bool {
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
pub fn default_child_trie_root<H: Hasher>(_storage_key: &[u8]) -> Vec<u8> {
	trie_root::<H, _, Vec<u8>, Vec<u8>>(core::iter::empty()).as_ref().iter().cloned().collect()
}

/// Determine a child trie root given its ordered contents, closed form. H is the default hasher, but a generic
/// implementation may ignore this type parameter and use other hashers.
pub fn child_trie_root<H: Hasher, I, A, B>(_storage_key: &[u8], input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
{
	trie_root::<H, _, _, _>(input).as_ref().iter().cloned().collect()
}

/// Determine a child trie root given a hash DB and delta values. H is the default hasher, but a generic implementation may ignore this type parameter and use other hashers.
pub fn child_delta_trie_root<H: Hasher, I, A, B, DB>(
	_storage_key: &[u8],
	db: &mut DB,
	root_vec: Vec<u8>,
	delta: I
) -> Result<Vec<u8>, Box<TrieError<H::Out>>> where
	I: IntoIterator<Item = (A, Option<B>)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	DB: hash_db::HashDB<H, trie_db::DBValue> + hash_db::PlainDB<H::Out, trie_db::DBValue>,
{
	let mut root = H::Out::default();
	root.as_mut().copy_from_slice(&root_vec); // root is fetched from DB, not writable by runtime, so it's always valid.

	{
		let mut trie = TrieDBMut::<H>::from_existing(&mut *db, &mut root)?;

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
pub fn for_keys_in_child_trie<H: Hasher, F: FnMut(&[u8]), DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	mut f: F
) -> Result<(), Box<TrieError<H::Out>>> where
	DB: hash_db::HashDBRef<H, trie_db::DBValue> + hash_db::PlainDBRef<H::Out, trie_db::DBValue>,
{
	let mut root = H::Out::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	let trie = TrieDB::<H>::new(&*db, &root)?;
	let iter = trie.iter()?;

	for x in iter {
		let (key, _) = x?;
		f(&key);
	}

	Ok(())
}

/// Record all keys for a given root.
pub fn record_all_keys<H: Hasher, DB>(
	db: &DB,
	root: &H::Out,
	recorder: &mut Recorder<H::Out>
) -> Result<(), Box<TrieError<H::Out>>> where
	DB: hash_db::HashDBRef<H, trie_db::DBValue>
{
	let trie = TrieDB::<H>::new(&*db, root)?;
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
pub fn read_child_trie_value<H: Hasher, DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8]
) -> Result<Option<Vec<u8>>, Box<TrieError<H::Out>>> where
	DB: hash_db::HashDBRef<H, trie_db::DBValue> + hash_db::PlainDBRef<H::Out, trie_db::DBValue>,
{
	let mut root = H::Out::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	Ok(TrieDB::<H>::new(&*db, &root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
}

/// Read a value from the child trie with given query.
pub fn read_child_trie_value_with<H: Hasher, Q: Query<H, Item=DBValue>, DB>(
	_storage_key: &[u8],
	db: &DB,
	root_slice: &[u8],
	key: &[u8],
	query: Q
) -> Result<Option<Vec<u8>>, Box<TrieError<H::Out>>> where
	DB: hash_db::HashDBRef<H, trie_db::DBValue> + hash_db::PlainDBRef<H::Out, trie_db::DBValue>,
{
	let mut root = H::Out::default();
	root.as_mut().copy_from_slice(root_slice); // root is fetched from DB, not writable by runtime, so it's always valid.

	Ok(TrieDB::<H>::new(&*db, &root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
}

// Utilities (not exported):

const EMPTY_TRIE: u8 = 0;
const LEAF_NODE_OFFSET: u8 = 1;
const LEAF_NODE_BIG: u8 = 127;
const EXTENSION_NODE_OFFSET: u8 = 128;
const EXTENSION_NODE_BIG: u8 = 253;
const BRANCH_NODE_NO_VALUE: u8 = 254;
const BRANCH_NODE_WITH_VALUE: u8 = 255;
const LEAF_NODE_THRESHOLD: u8 = LEAF_NODE_BIG - LEAF_NODE_OFFSET;
const EXTENSION_NODE_THRESHOLD: u8 = EXTENSION_NODE_BIG - EXTENSION_NODE_OFFSET;	//125
const LEAF_NODE_SMALL_MAX: u8 = LEAF_NODE_BIG - 1;
const EXTENSION_NODE_SMALL_MAX: u8 = EXTENSION_NODE_BIG - 1;

fn take<'a>(input: &mut &'a[u8], count: usize) -> Option<&'a[u8]> {
	if input.len() < count {
		return None
	}
	let r = &(*input)[..count];
	*input = &(*input)[count..];
	Some(r)
}

fn partial_to_key(partial: &[u8], offset: u8, big: u8) -> Vec<u8> {
	let nibble_count = (partial.len() - 1) * 2 + if partial[0] & 16 == 16 { 1 } else { 0 };
	let (first_byte_small, big_threshold) = (offset, (big - offset) as usize);
	let mut output = [first_byte_small + nibble_count.min(big_threshold) as u8].to_vec();
	if nibble_count >= big_threshold { output.push((nibble_count - big_threshold) as u8) }
	if nibble_count % 2 == 1 {
		output.push(partial[0] & 0x0f);
	}
	output.extend_from_slice(&partial[1..]);
	output
}

fn branch_node(has_value: bool, has_children: impl Iterator<Item = bool>) -> [u8; 3] {
	let first = if has_value {
		BRANCH_NODE_WITH_VALUE
	} else {
		BRANCH_NODE_NO_VALUE
	};
	let mut bitmap: u16 = 0;
	let mut cursor: u16 = 1;
	for v in has_children {
		if v { bitmap |= cursor }
		cursor <<= 1;
	}
	[first, (bitmap % 256 ) as u8, (bitmap / 256 ) as u8]
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Compact};
	use substrate_primitives::Blake2Hasher;
	use hash_db::{HashDB, Hasher};
	use trie_db::{DBValue, TrieMut, Trie};
	use trie_standardmap::{Alphabet, ValueMode, StandardMap};
	use hex_literal::hex;

	fn check_equivalent(input: &Vec<(&[u8], &[u8])>) {
		{
			let closed_form = trie_root::<Blake2Hasher, _, _, _>(input.clone());
			let d = unhashed_trie::<Blake2Hasher, _, _, _>(input.clone());
			println!("Data: {:#x?}, {:#x?}", d, Blake2Hasher::hash(&d[..]));
			let persistent = {
				let mut memdb = MemoryDB::default();
				let mut root = Default::default();
				let mut t = TrieDBMut::<Blake2Hasher>::new(&mut memdb, &mut root);
				for (x, y) in input.iter().rev() {
					t.insert(x, y).unwrap();
				}
				t.root().clone()
			};
			assert_eq!(closed_form, persistent);
		}
	}

	fn check_iteration(input: &Vec<(&[u8], &[u8])>) {
		let mut memdb = MemoryDB::default();
		let mut root = Default::default();
		{
			let mut t = TrieDBMut::<Blake2Hasher>::new(&mut memdb, &mut root);
			for (x, y) in input.clone() {
				t.insert(x, y).unwrap();
			}
		}
		{
			let t = TrieDB::<Blake2Hasher>::new(&mut memdb, &root).unwrap();
			assert_eq!(
				input.iter().map(|(i, j)| (i.to_vec(), j.to_vec())).collect::<Vec<_>>(),
				t.iter().unwrap().map(|x| x.map(|y| (y.0, y.1.to_vec())).unwrap()).collect::<Vec<_>>()
			);
		}
	}

	#[test]
	fn default_trie_root() {
		let mut db = MemoryDB::default();
		let mut root = <Blake2Hasher as Hasher>::Out::default();
		let mut empty = TrieDBMut::<Blake2Hasher>::new(&mut db, &mut root);
		empty.commit();
		let root1 = empty.root().as_ref().to_vec();
		let root2: Vec<u8> = trie_root::<Blake2Hasher, _, Vec<u8>, Vec<u8>>(std::iter::empty()).as_ref().iter().cloned().collect();

		assert_eq!(root1, root2);
	}

	#[test]
	fn empty_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![];
		check_equivalent(&input);
		check_iteration(&input);
	}

	#[test]
	fn leaf_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0xbb][..])];
		check_equivalent(&input);
		check_iteration(&input);
	}

	#[test]
	fn branch_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0x10][..]), (&[0xba][..], &[0x11][..])];
		check_equivalent(&input);
		check_iteration(&input);
	}

	#[test]
	fn extension_and_branch_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &[0x10][..]), (&[0xab][..], &[0x11][..])];
		check_equivalent(&input);
		check_iteration(&input);
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
		d.sort_unstable_by(|&(ref a, _), &(ref b, _)| a.cmp(b));
		let dr = d.iter().map(|v| (&v.0[..], &v.1[..])).collect();
		check_equivalent(&dr);
		check_iteration(&dr);
	}

	#[test]
	fn extension_and_branch_with_value_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &[0xa0][..]),
			(&[0xaa, 0xaa][..], &[0xaa][..]),
			(&[0xaa, 0xbb][..], &[0xab][..])
		];
		check_equivalent(&input);
		check_iteration(&input);
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
		check_equivalent(&input);
		check_iteration(&input);
	}

	#[test]
	fn single_long_leaf_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]), (&[0xba][..], &[0x11][..])];
		check_equivalent(&input);
		check_iteration(&input);
	}

	#[test]
	fn two_long_leaves_is_equivalent() {
		let input: Vec<(&[u8], &[u8])> = vec![
			(&[0xaa][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..]),
			(&[0xba][..], &b"ABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABCABC"[..])
		];
		check_equivalent(&input);
		check_iteration(&input);
	}

	fn populate_trie<'db>(
		db: &'db mut HashDB<Blake2Hasher, DBValue>,
		root: &'db mut <Blake2Hasher as Hasher>::Out,
		v: &[(Vec<u8>, Vec<u8>)]
	) -> TrieDBMut<'db, Blake2Hasher> {
		let mut t = TrieDBMut::<Blake2Hasher>::new(db, root);
		for i in 0..v.len() {
			let key: &[u8]= &v[i].0;
			let val: &[u8] = &v[i].1;
			t.insert(key, val).unwrap();
		}
		t
	}

	fn unpopulate_trie<'db>(t: &mut TrieDBMut<'db, Blake2Hasher>, v: &[(Vec<u8>, Vec<u8>)]) {
		for i in v {
			let key: &[u8]= &i.0;
			t.remove(key).unwrap();
		}
	}

	#[test]
	fn random_should_work() {
		let mut seed = <Blake2Hasher as Hasher>::Out::zero();
		for test_i in 0..10000 {
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

			let real = trie_root::<Blake2Hasher,_, _, _>(x.clone());
			let mut memdb = MemoryDB::default();
			let mut root = Default::default();
			let mut memtrie = populate_trie(&mut memdb, &mut root, &x);

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
			unpopulate_trie(&mut memtrie, &x);
			memtrie.commit();
			if *memtrie.root() != <NodeCodec<Blake2Hasher> as trie_db::NodeCodec<Blake2Hasher>>::hashed_null_node() {
				println!("- TRIE MISMATCH");
				println!("");
				println!("{:?} vs {:?}", memtrie.root(), <NodeCodec<Blake2Hasher> as trie_db::NodeCodec<Blake2Hasher>>::hashed_null_node());
				for i in &x {
					println!("{:#x?} -> {:#x?}", i.0, i.1);
				}
			}
			assert_eq!(*memtrie.root(), <NodeCodec<Blake2Hasher> as trie_db::NodeCodec<Blake2Hasher>>::hashed_null_node());
		}
	}

	fn to_compact(n: u8) -> u8 {
		Compact(n).encode()[0]
	}

	#[test]
	fn codec_trie_empty() {
		let input: Vec<(&[u8], &[u8])> = vec![];
		let trie = unhashed_trie::<Blake2Hasher, _, _, _>(input);
		println!("trie: {:#x?}", trie);
		assert_eq!(trie, vec![0x0]);
	}

	#[test]
	fn codec_trie_single_tuple() {
		let input = vec![
			(vec![0xaa], vec![0xbb])
		];
		let trie = unhashed_trie::<Blake2Hasher, _, _, _>(input);
		println!("trie: {:#x?}", trie);

		assert_eq!(trie, vec![
			0x03,					// leaf (0x01) with (+) key of 2 nibbles (0x02)
			0xaa,					// key data
			to_compact(1),			// length of value in bytes as Compact
			0xbb					// value data
		]);
	}

	#[test]
	fn codec_trie_two_tuples_disjoint_keys() {
		let input = vec![(&[0x48, 0x19], &[0xfe]), (&[0x13, 0x14], &[0xff])];
		let trie = unhashed_trie::<Blake2Hasher, _, _, _>(input);
		println!("trie: {:#x?}", trie);

		let mut ex = Vec::<u8>::new();
		ex.push(0xfe);									// branch, no value
		ex.push(0x12);									// slots 1 & 4 are taken from 0-7
		ex.push(0x00);									// no slots from 8-15
		ex.push(to_compact(0x05));						// first slot: LEAF, 5 bytes long.
		ex.push(0x04);									// leaf with 3 nibbles
		ex.push(0x03);									// first nibble
		ex.push(0x14);									// second & third nibble
		ex.push(to_compact(0x01));						// 1 byte data
		ex.push(0xff);									// value data
		ex.push(to_compact(0x05));						// second slot: LEAF, 5 bytes long.
		ex.push(0x04);									// leaf with 3 nibbles
		ex.push(0x08);									// first nibble
		ex.push(0x19);									// second & third nibble
		ex.push(to_compact(0x01));						// 1 byte data
		ex.push(0xfe);									// value data

		assert_eq!(trie, ex);
	}

	#[test]
	fn iterator_works() {
		let pairs = vec![
			(hex!("0103000000000000000464").to_vec(), hex!("0400000000").to_vec()),
			(hex!("0103000000000000000469").to_vec(), hex!("0401000000").to_vec()),
		];

		let mut mdb = MemoryDB::default();
		let mut root = Default::default();
		let _ = populate_trie(&mut mdb, &mut root, &pairs);

		let trie = TrieDB::<Blake2Hasher>::new(&mdb, &root).unwrap();

		let iter = trie.iter().unwrap();
		let mut iter_pairs = Vec::new();
		for pair in iter {
			let (key, value) = pair.unwrap();
			iter_pairs.push((key, value.to_vec()));
		}

		assert_eq!(pairs, iter_pairs);
	}
}
