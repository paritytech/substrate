// This file is part of Substrate.

// Copyright (C) 2015-2022 Parity Technologies (UK) Ltd.
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

//! Bad mmr implementation please don't use for real use case :)
//! - size of node stored is too small
//! - compact encoding is not as compact as should be
//! ...

/// Mmr with storage model similar to triedb (but no management of hash collision: would only
/// work with paritydb rc backend, yet with this partial code there is no removal written, so
/// should be fine with rocksdb too).
use hash_db::{HashDB, HashDBRef, Hasher};
use sp_std::{collections::vec_deque::VecDeque, vec, vec::Vec};

pub type DBValue = Vec<u8>;

pub struct MmrDB<'db, H: Hasher> {
	db: &'db dyn HashDBRef<H, DBValue>,
	root: &'db H::Out,
	number_element: u64,
}

pub fn empty_root<H: Hasher>() -> H::Out {
	H::hash(&[])
}

pub fn read_child_trie_value<H, DB>(
	db: &DB,
	root: &H::Out,
	number_element: u64,
	at: u64,
) -> Option<Vec<u8>>
where
	H: Hasher,
	DB: hash_db::HashDBRef<H, DBValue>,
{
	MmrDB { db: &*db, root, number_element }.get(at)
}

pub fn child_delta_trie_root<H: Hasher, DB, I, A>(
	db: &mut DB,
	mut root: H::Out,
	number_element: u64,
	delta: I,
) -> Result<(u64, H::Out), &'static str>
where
	I: IntoIterator<Item = A>,
	A: sp_std::borrow::Borrow<[u8]>,
	DB: hash_db::HashDB<H, trie_db::DBValue>,
{
	let mut mmr =
		MmrDBMut { peaks: Default::default(), db: &mut *db, root: &mut root, number_element };
	for v in delta.into_iter() {
		mmr.push(v.borrow()).ok_or("error calculating root")?;
	}
	mmr.commit();
	Ok((mmr.number_element, root))
}

impl<'db, H: Hasher> MmrDB<'db, H> {
	pub fn get(&self, index: u64) -> Option<DBValue> {
		if index < self.number_element {
			let num_peaks = self.number_element.count_ones();
			let mut skips = num_peaks - 1;
			let max_depth = 64 - (self.number_element - 1).leading_zeros();
			let mut node = self.db.get(self.root, Default::default())?;
			let mut hash = H::Out::default();
			let hash_len = hash.as_ref().len();
			let mut skip_next = false;
			for i in (0..max_depth).rev() {
				let ix = (index & 1 << i) > 0;
				if !ix && skip_next {
					if ((self.number_element - 1) & 1 << i) == 0 {
						continue
					} else {
						skip_next = false;
					}
				}
				if ix {
					if skips > 0 {
						skips -= 1;
						skip_next = true;
					}
				} else {
					skips = 0;
				}
				if node.len() != hash_len * 2 {
					// incorrect node, bug in impl
					panic!("Invalid build mmr");
				}
				let ix = ix as usize;
				hash.as_mut().copy_from_slice(&node[ix * hash_len..(ix + 1) * hash_len]);
				node = self.db.get(&hash, Default::default())?;
			}
			Some(node)
		} else {
			None
		}
	}
}

pub struct MmrDBMut<'db, H: Hasher> {
	pub peaks: VecDeque<H::Out>,
	pub db: &'db mut dyn HashDB<H, DBValue>,
	pub root: &'db mut H::Out,
	pub number_element: u64,
}

impl<'db, H: Hasher> MmrDBMut<'db, H> {
	pub fn empty(db: &'db mut dyn HashDB<H, DBValue>, root: &'db mut H::Out) -> Self {
		MmrDBMut { db, root, peaks: Default::default(), number_element: 0 }
	}
	pub fn get(&self, index: u64) -> Option<DBValue> {
		MmrDB {
			db: &self.db,
			root: &*self.root,
			number_element: self.number_element,
		}.get(index)
	}

	pub fn push(&mut self, value: &[u8]) -> Option<()> {
		let num_peaks = self.number_element.count_ones();
		if num_peaks == 0 {
			let leaf = self.db.insert(Default::default(), value);
			self.peaks.push_back(leaf);
			self.number_element += 1;
			return Some(())
		}
		if self.number_element > 0 && self.peaks.len() == 0 {
			// lazy init: don't feed proof if no push.
			if num_peaks == 1 {
				self.peaks.push_back(self.root.clone());
			} else {
				let mut hash = H::Out::default();
				let mut node = self.db.get(self.root, Default::default())?;
				let hash_len = hash.as_ref().len();
				for _ in 0..num_peaks - 1 {
					if node.len() != hash_len * 2 {
						// incorrect node, bug in impl
						panic!("Invalid build mmr");
					}
					let mut left = H::Out::default();
					left.as_mut().copy_from_slice(&node[..hash_len]);
					self.peaks.push_back(left);
					hash.as_mut().copy_from_slice(&node[hash_len..]);
					node = self.db.get(&hash, Default::default())?;
				}
				self.peaks.push_back(hash);
			}
		}
		let hash_len = H::Out::default().as_ref().len();
		let mut node = vec![0u8; hash_len * 2];
		let leaf = self.db.insert(Default::default(), value);

		let new_num_peaks = (self.number_element + 1).count_ones();
		if new_num_peaks == num_peaks {
			// pair with last
			let r = self.peaks.pop_back().unwrap();
			node[..hash_len].copy_from_slice(r.as_ref());
			node[hash_len..].copy_from_slice(leaf.as_ref());
			let n = self.db.insert(Default::default(), node.as_slice());
			self.peaks.push_back(n);
		} else if new_num_peaks > num_peaks {
			self.peaks.push_back(leaf);
		} else {
			self.peaks.push_back(leaf);
			while self.peaks.len() as u32 != new_num_peaks {
				let n = self.peaks.pop_back().unwrap();
				let r = self.peaks.pop_back().unwrap();
				node[..hash_len].copy_from_slice(r.as_ref());
				node[hash_len..].copy_from_slice(n.as_ref());
				let new = self.db.insert(Default::default(), node.as_slice());
				self.peaks.push_back(new);
			}
		}
		self.number_element += 1;
		Some(())
	}

	pub fn commit(&mut self) {
		if self.peaks.len() == 0 {
			return
		}
		let mut with = self.peaks.pop_back().unwrap();
		let hash_len = H::Out::default().as_ref().len();
		let mut node = vec![0u8; hash_len * 2];
		while let Some(r) = self.peaks.pop_back() {
			node[..hash_len].copy_from_slice(r.as_ref());
			node[hash_len..].copy_from_slice(with.as_ref());
			with = self.db.insert(Default::default(), node.as_slice());
		}
		*self.root = with;
		self.peaks.clear();
	}

	// TODO move to MMr non mut
	// Warning this is most probably bugged
	pub fn encode_compact(&self) -> Result<Vec<Vec<u8>>, &'static str> {
		// Some dummy format with one byte as enum, non optimal
		let mut stack = Vec::new();
		let mut result = Vec::new();
		let mut hash = H::Out::default();
		let hash_len = hash.as_ref().len();
		// TODO corner case single value?
		// (node, depth, went_left)
		let mut node =
			(self.db.get(self.root, Default::default()).ok_or("Missing mmr root")?, 0, false);
		let mut descend = true;

		let max_depth = 64 - (self.number_element - 1).leading_zeros();
		loop {
			if descend {
				if node.1 == max_depth {
					// value
					let mut node = node.0.clone();
					node.insert(0, 4);
					result.push(node);
					descend = false;
				} else {
					match node.0.len() {
						x if 2 * hash_len == x => {
							hash.as_mut().copy_from_slice(&node.0[..hash_len]);
							if let Some(child) = self.db.get(&hash, Default::default()) {
								let mut s = vec![1];
								s.extend_from_slice(&node.0[hash_len..]);
								stack.push((s, node.1, node.2)); // left
								node = (child, node.1 + 1, true)
							} else {
								hash.as_mut().copy_from_slice(&node.0[hash_len..]);
								if let Some(child) = self.db.get(&hash, Default::default()) {
									let mut s = vec![0];
									s.extend_from_slice(&node.0[..hash_len]);
									stack.push((s, node.1, node.2)); // right only
									let mut new_depth = node.1 + 1;
									if !node.2 {
										while new_depth < max_depth &&
											(self.number_element - 1) &
												(1 << (max_depth - 1 - new_depth)) == 0
										{
											new_depth += 1;
										}
									}
									node = (child, new_depth, node.2);
								} else {
									unreachable!("no child in node, node should not be here");
									// TODO just descend = false; ?
									/*								 // value
									let mut node = node.clone();
									node.insert(0, 4);
									result.push(node);
									descend = false;*/
								}
							}
						},
						_ => {
							unreachable!("would be catch in depth check");
							// should be a value
							/*let mut node = node.0.clone();
							node.insert(0, 4);
							result.push(node);
							descend = false;*/
						},
					}
				}
			} else {
				if let Some(node_stacked) = stack.pop() {
					match node_stacked.0.len() {
						x if hash_len + 1 == x && node_stacked.0[0] == 1 => {
							hash.as_mut().copy_from_slice(&node_stacked.0[1..]);
							if let Some(child) = self.db.get(&hash, Default::default()) {
								stack.push((vec![2], node_stacked.1, node_stacked.2)); // 2 for both child
								let mut new_depth = node_stacked.1 + 1;
								if !node_stacked.2 {
									while new_depth < max_depth &&
										(self.number_element - 1) &
											(1 << (max_depth - 1 - new_depth)) == 0
									{
										new_depth += 1;
									}
								}
								node = (child, new_depth, node_stacked.2);
								descend = true;
							} else {
								// just no child continue unstack
								result.push(node_stacked.0);
								/*								// value
								let mut node = node_stacked.0.clone();
								node.insert(0, 4);
								result.push(node);*/
							}
						},
						_ => {
							result.push(node_stacked.0);
						},
					}
				} else {
					break
				}
			}
		}
		Ok(result)
	}

	pub fn decode_compact<'a, DB>(
		db: &mut DB,
		_number_element: u64,
		encoded: &mut impl Iterator<Item = &'a [u8]>,
	) -> Result<H::Out, &'static str>
	where
		DB: HashDB<H, DBValue>,
	{
		let mut parent_hash: Option<H::Out> = None;
		let mut left_hash: Option<H::Out> = None;
		for node in encoded {
			match node[0] {
				0 => {
					// right hash
					if let Some(right) = parent_hash.take() {
						let mut left = node[1..].to_vec();
						left.extend_from_slice(right.as_ref());
						parent_hash = Some(db.insert(Default::default(), left.as_slice()));
					} else {
						return Err("node without child in proof")
					}
				},
				1 => {
					// left hash
					if let Some(left) = parent_hash.take() {
						let mut left = left.as_ref().to_vec();
						left.extend_from_slice(&node[1..]);
						parent_hash = Some(db.insert(Default::default(), left.as_slice()));
					} else {
						return Err("node without child in proof")
					}
				},
				2 => {
					// branch no hash
					if let (Some(left), Some(right)) = (left_hash.take(), parent_hash) {
						let mut node = left.as_ref().to_vec();
						node.extend_from_slice(right.as_ref());
						parent_hash = Some(db.insert(Default::default(), node.as_slice()));
					} else {
						return Err("bad format")
					}
				},
				3 => {
					// root
					break
				},
				4 => {
					if parent_hash.is_some() {
						left_hash = parent_hash;
					}
					// value
					parent_hash = Some(db.insert(Default::default(), &node[1..]));
				},
				_ => return Err("unexpected header byte"),
			}
		}
		parent_hash.ok_or("invalid mmr compact proof")
	}
}

#[test]
fn simple_test() {
	use sp_runtime::traits::BlakeTwo256;
	let mut db = memory_db::MemoryDB::<BlakeTwo256, memory_db::HashKey<_>, Vec<u8>>::default();
	let mut root = <BlakeTwo256 as Hasher>::Out::default();
	let mut trie_db =
		MmrDBMut { db: &mut db, root: &mut root, peaks: Default::default(), number_element: 0 };
	let nb = 100;
	for i in 0u64..nb {
		let val = i.to_le_bytes();

		trie_db.push(&val[..]); // TODO test with multiple push (iter until nb / nb_psuh).
		trie_db.commit();

		for j in 0u64..i + 1 {
			let val = j.to_le_bytes().to_vec();
			assert_eq!((trie_db.get(j), i, j), (Some(val), i, j));
		}
	}
}
