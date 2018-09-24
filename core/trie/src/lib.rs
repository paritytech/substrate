// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

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

//! Generates trie root.
//!
//! This module should be used to generate trie root hash.

extern crate trie_root;
extern crate parity_codec as codec;
extern crate trie_db;
extern crate hash_db;

#[cfg(test)]
extern crate memory_db;
#[cfg(test)]
extern crate substrate_primitives;
#[cfg(test)]
extern crate trie_standardmap;

mod error;
mod node_header;
mod node_codec;
mod trie_stream;

use hash_db::Hasher;
pub use error::Error;
pub use node_codec::NodeCodec;
pub use trie_stream::TrieStream;

pub type TrieDB<'a, H> = trie_db::TrieDB<'a, H, NodeCodec<H>>;
pub type TrieDBMut<'a, H> = trie_db::TrieDBMut<'a, H, NodeCodec<H>>;
pub type FatDB<'a, H> = trie_db::FatDB<'a, H, NodeCodec<H>>;
pub type FatDBMut<'a, H> = trie_db::FatDBMut<'a, H, NodeCodec<H>>;
pub type SecTrieDB<'a, H> = trie_db::SecTrieDB<'a, H, NodeCodec<H>>;
pub type SecTrieDBMut<'a, H> = trie_db::SecTrieDBMut<'a, H, NodeCodec<H>>;
pub type Lookup<'a, H, Q> = trie_db::Lookup<'a, H, NodeCodec<H>, Q>;

pub fn trie_root<H: Hasher, I, A, B>(input: I) -> H::Out where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord + trie_root::DebugIfStd,
	B: AsRef<[u8]> + trie_root::DebugIfStd,
{
	trie_root::trie_root::<H, TrieStream, _, _, _>(input)
}

pub fn unhashed_trie<H: Hasher, I, A, B>(input: I) -> Vec<u8> where
	I: IntoIterator<Item = (A, B)> + trie_root::DebugIfStd,
	A: AsRef<[u8]> + Ord + trie_root::DebugIfStd,
	B: AsRef<[u8]> + trie_root::DebugIfStd,
{
	trie_root::unhashed_trie::<H, TrieStream, _, _, _>(input)
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
	let mut output = vec![first_byte_small + nibble_count.min(big_threshold) as u8];
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

/*
// TODO: Remove
fn compact_len(n: usize) -> usize {
	match n {
		0...0b00111111 => 1,
		0...0b00111111_11111111 => 2,
		_ => 4
	}
}

/// Returns the size of the node that `data` begins with, `Hash` if it's a hash, or `None` if no node exists.
fn node_len(data: &[u8], hash_len: usize) -> Option<(usize, bool)> {
	use codec_triestream::{EMPTY_TRIE, LEAF_NODE_OFFSET, LEAF_NODE_BIG, EXTENSION_NODE_OFFSET,
		EXTENSION_NODE_BIG, BRANCH_NODE_NO_VALUE, BRANCH_NODE_WITH_VALUE,
		LEAF_NODE_SMALL_MAX, EXTENSION_NODE_SMALL_MAX};

//	println!("node_len({:#x?})", data);

	if data.len() < 1 {
		return None
	}
	Some((match data[0] {
		EMPTY_TRIE => return Some((1 + hash_len, true)),

		i @ LEAF_NODE_OFFSET ... LEAF_NODE_SMALL_MAX => {
			let nibbles_len = (((i - LEAF_NODE_OFFSET) + 1) / 2) as usize;
			let value_len = <Compact<u32>>::decode(&mut &data[1 + nibbles_len..])?.0 as usize;
			1 + nibbles_len + compact_len(value_len) + value_len
		}
		i @ LEAF_NODE_BIG => {
			let nibbles_len = ((((i - LEAF_NODE_OFFSET) as usize + data[1] as usize) + 1) / 2) as usize;
			let value_len = <Compact<u32>>::decode(&mut &data[2 + nibbles_len..])?.0 as usize;
			2 + nibbles_len + compact_len(value_len) + value_len
		}
		i @ EXTENSION_NODE_OFFSET ... EXTENSION_NODE_SMALL_MAX => {
			let nibbles_len = (((i - EXTENSION_NODE_OFFSET) + 1) / 2) as usize;
			1 + nibbles_len + node_len(&data[1 + nibbles_len..], hash_len)?.0
		}
		i @ EXTENSION_NODE_BIG => {
			let nibbles_len = ((((i - EXTENSION_NODE_OFFSET) as usize + data[1] as usize) + 1) / 2) as usize;
			2 + nibbles_len + node_len(&data[2 + nibbles_len..], hash_len)?.0
		}

		x @ BRANCH_NODE_NO_VALUE | x @ BRANCH_NODE_WITH_VALUE => {
			let child_count = data[1].count_ones() + data[2].count_ones();
			let mut offset = 3;
			println!("node_len: branch(children={})", child_count);
			if x == BRANCH_NODE_WITH_VALUE {
				let value_len = <Compact<u32>>::decode(&mut &data[3..])?.0 as usize;
				println!("node_len: branch: has_value({})", value_len);
				offset += compact_len(value_len) + value_len;
			}
			for _ in 0..child_count {
				offset += node_len(&data[offset..], hash_len)?.0;
			}
			offset
		}

		_ => unreachable!(),
	}, false))
}
*/
#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Compact};
	use substrate_primitives::Blake2Hasher;
	use memory_db::MemoryDB;
	use hash_db::{HashDB, Hasher};
	use trie_db::{DBValue, TrieMut, Trie};
	use trie_standardmap::{Alphabet, ValueMode, StandardMap};

	fn check_equivalent(input: &Vec<(&[u8], &[u8])>) {
/*		{
			let closed_form = trie_root::<Blake2Hasher, TrieStream, _, _, _>(input.clone());
			let d = unhashed_trie::<Blake2Hasher, _, _, _>(input.clone());
			println!("Data: {:#x?}, {:#x?}", d, Blake2Hasher::hash(&d[..]));
			let persistent = {
				let mut memdb = MemoryDB::default();
				let mut root = Default::default();
				let mut t = TrieDBMut::<Blake2Hasher, NodeCodec<Blake2Hasher>>::new(&mut memdb, &mut root);
				for (x, y) in input {
					t.insert(x, y).unwrap();
				}
				t.root().clone()
			};
			assert_eq!(closed_form, persistent);
		}*/
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
		let mut seed = <Blake2Hasher as Hasher>::Out::new();
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
			}.make_with(&mut seed.0);

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

	// TODO: make other tests work.
/*
	#[test]
	fn learn_codec_trie_single_item() {
		let input: Vec<(&[u8], &[u8])> = vec![(&[0x13], &[0x14])];
		let trie = unhashed_trie::<Blake2Hasher, _, _, _>(input);
		println!("[learn_codec_trie_single_item] 1st byte of trie:\n{:#010b}\n trie: {:#x?}", trie[0], trie );
		assert_eq!(trie, vec![
			0b10_10_0000, 			// variant: leaf, even payload length
			to_compact(0x01), 		// key length: 1 bytes
			0x13,					// key
			to_compact(0x01), 		// value length: 1 bytes
			0x14					// value
		]);

		let input = vec![(
			vec![0x12, 0x12, 0x12, 0x12, 0x13],	// key
			vec![0xff, 0xfe, 0xfd, 0xfc]		// val
		)];
		let trie = unhashed_trie::<Blake2Hasher, _, _, _>(input);
		assert_eq!(trie, vec![
			0b10_10_0000, 			// variant: leaf, even payload length
			to_compact(0x05), 		// key length: 5 bytes
			0x12, 0x12, 0x12, 0x12, 0x13,
			to_compact(0x04), 		// value length: 4 bytes
			0xff, 0xfe, 0xfd, 0xfc
		]);
	}

	#[test]
	fn learn_rlp_trie_full_example() {
		let input = vec![
			(vec![0xa7, 0x11, 0x35, 0x5], vec![45]),
			(vec![0xa7, 0x7d, 0x33, 0x7], vec![1]),
			(vec![0xa7, 0xf9, 0x36, 0x5], vec![11]),
			(vec![0xa7, 0x7d, 0x39, 0x7], vec![12]),
		];
		/*
		Expected trie:
			Extension, 0xa7
			Branch
				1: Leaf ([0x01, 0x35, 0x5], 45)
				7: Extension, d3
					Branch
						3: Leaf ([0x03, 0x07], 1)
						9: Leaf ([0x09, 0x07], 12)
				f: Leaf (0x09, 0x36, 0x5, 11)
		*/
		let rlp_trie = unhashed_trie::<Blake2Hasher, RlpTrieStream, _, _, _>(input);
		println!("rlp trie: {:#x?}", rlp_trie);
		// TODO: finish
		// assert_eq!(rlp_trie, vec![
		// 	0xc0 + 36,
		// 	0x80 + 2,
		// 	0b0000_0000,	// HPE flag-byte
		// 	0xa7,			// partial key; end ext
		// 	0x80 + 32, 		// begin_list(17) - why 32? hash len?
		// 	0x80,			// slot 0: empty
		// 	0xc0 + 7,		// slot 1: start list(2) to build leaf
		// 	0x80 + 3,		// value marker + length
		// 	0x31, 			// HPE byte 0b00_11_0001 (leaf, odd, 1 in lower nibble)
		// 	0x35, 0x05,		// rest of key,
		// 	0x80 + 1,		// value marker
		// 	45,				// value
		// 	0x80,			// slot 2: empty
		// 	0x80,			// slot 3: empty
		// 	0x80,			// slot 4: empty
		// 	0x80,			// slot 5: empty
		// 	0x80,			// slot 6: empty
		// 	0xc0 + 0,		// slot 7: extension, begin_list(2)
		// 	0b0000_0000,	// HPE flag-byte
		// 	0x80 + 2,		// value marker + length
		// 	0xd3,			// partial key; end ext
		// 	0xc0 + 0		// branch node; begin list
		// … … …
		// ]);

	}

	#[test]
	fn learn_codec_trie_full_example() {
		let input = vec![
			(vec![0xa7, 0x11, 0x35, 0x5], vec![45]),
			(vec![0xa7, 0x7d, 0x33, 0x7], vec![1]),
			(vec![0xa7, 0xf9, 0x36, 0x5], vec![11]),
			(vec![0xa7, 0x7d, 0x39, 0x7], vec![12]),
		];
		/*
		Expected trie:
			Extension, 0xa7
			Branch
				1: Leaf ([0x01, 0x35, 0x5], 45)
				7: Extension, d3
					Branch
						3: Leaf ([0x03, 0x07], 1)
						9: Leaf ([0x09, 0x07], 12)
				f: Leaf (0x09, 0x36, 0x5, 11)
		*/
		let codec_trie = unhashed_trie::<Blake2Hasher, _, _, _>(input.clone());
		println!("codec trie: {:#x?}", codec_trie);

		assert_eq!(codec_trie, vec![
			0x80,				// 0b10000000 => extension
			to_compact(0x1),	// length 1
			0xa7,				// payload: a7
			to_compact(62),		// length 62 bytes
			0x40,				// Branch node: 0b01_00_0000
			0x0,				// slot 0: empty node
			to_compact(0x6),	// slot 1: 6 bytes follow
			0xb1,				// 0xb1 == 177 == 0b1011_0001 => 0b10_11_xxxx, leaf, odd length + 0001
			to_compact(0x2),	// length: 2 bytes
			0x35,				// key payload
			0x5,
			to_compact(0x1),	// value length: 1 byte
			0x2d,				// value: 45; 12th byte, ends slot 1
			0x0,				// slot 2
			0x0,				// slot 3
			0x0,				// slot 4
			0x0,				// slot 5
			0x0,				// slot 6
			to_compact(32),		// slot 7; item of length 32
			0x80,				// extension node, 0b10000000
			to_compact(0x1),	// key length: 1 byte
			0xd3,				// key payload, 0xd3
			to_compact(28),		// item of length 28
			0x40,				// Branch node: 0b01_00_0000
			0x0,				// slot 0
			0x0,				// slot 1
			0x0,				// slot 2
			to_compact(0x5),	// slot 3, item of length 5
			0xa0,				// payload, 0b1010_0000: leaf node, even length
			to_compact(0x1),	// key length: 1 byte
			0x7,				// partial key payload: 7
			to_compact(0x1),	// value length: 1 byte
			0x1,				// value payload: 1
			0x0,				// slot 4
			0x0,				// slot 5
			0x0,				// slot 6
			0x0,				// slot 7
			0x0,				// slot 8
			to_compact(0x5),	// slot 9,  item of length 11
			0xa0,				// payload, 0b1010_0000: lead node, even length
			to_compact(0x1),	// key length 1 byte
			0x7,				// key payload: 7
			to_compact(0x1),	// value length: 1 byte
			0xc,				// value payload: 12
			0x0,				// slot 11
			0x0,				// slot 12
			0x0,				// slot 13
			0x0,				// slot 14
			0x0,				// slot 15; end second branch node
			0x0,				// slot 16; second branch value slot
			0x0,				// slot 8 (first branch)
			0x0,				// slot 9
			0x0,				// slot 10
			0x0,				// slot 11
			0x0,				// slot 12
			0x0,				// slot 13
			0x0,				// slot 14
			0x0,				// slot 15
			to_compact(0x6),	// slot 16; first branch value slot; item of length 12
			0xb9,				// 0xb9 == 185 == 0b1011_1001 => Leaf node, odd number, partial key payload = 9
			to_compact(0x2),	// length: 2 bytes
			0x36,				// payload: 0x36, 0x5
			0x5,
			to_compact(0x1),	// length: 1 byte
			0xb,				// value: 11
			0x0
		]);
	}
	*/
}