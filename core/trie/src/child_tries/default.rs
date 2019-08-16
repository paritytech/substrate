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

//! Default child trie declaration. That is, the child trie that uses
//! the same structure of root trie.

use super::ChildTrie;
use crate::{TrieHash, TrieError, TrieDBMut, TrieDB};
use rstd::boxed::Box;
use rstd::vec::Vec;
use trie_db::{TrieConfiguration, DBValue, Query, Trie, TrieMut};
use hash_db::{HashDB, HashDBRef, PlainDB, PlainDBRef};

/// Default child trie.
pub struct DefaultChildTrie;

impl ChildTrie for DefaultChildTrie {
	fn default_root<L: TrieConfiguration>(&self) -> Vec<u8> {
		L::trie_root::<_, Vec<u8>, Vec<u8>>(core::iter::empty()).as_ref().iter().cloned().collect()
	}

	fn root<L: TrieConfiguration, I, A, B>(&self, input: I) -> Vec<u8> where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>
	{
		L::trie_root(input).as_ref().iter().cloned().collect()
	}

	fn delta_root<L: TrieConfiguration, I, A, B, DB>(
		&self, db: &mut DB, root_vec: Vec<u8>, delta: I
	) -> Result<Vec<u8>, Box<TrieError<L>>> where
		I: IntoIterator<Item = (A, Option<B>)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
		DB: HashDB<L::Hash, DBValue> + PlainDB<TrieHash<L>, DBValue>
	{
		let mut root = TrieHash::<L>::default();
		// root is fetched from DB, not writable by runtime, so it's always valid.
		root.as_mut().copy_from_slice(&root_vec);

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

	fn for_keys<L: TrieConfiguration, F: FnMut(&[u8]), DB>(
		&self, db: &DB, root_slice: &[u8], mut f: F
	) -> Result<(), Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>
	{
		let mut root = TrieHash::<L>::default();
		// root is fetched from DB, not writable by runtime, so it's always valid.
		root.as_mut().copy_from_slice(root_slice);

		let trie = TrieDB::<L>::new(&*db, &root)?;
		let iter = trie.iter()?;

		for x in iter {
			let (key, _) = x?;
			f(&key);
		}

		Ok(())
	}

	fn read_value<L: TrieConfiguration, DB>(
		&self, db: &DB, root_slice: &[u8], key: &[u8]
	) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>
	{
		let mut root = TrieHash::<L>::default();
		// root is fetched from DB, not writable by runtime, so it's always valid.
		root.as_mut().copy_from_slice(root_slice);

		Ok(TrieDB::<L>::new(&*db, &root)?.get(key).map(|x| x.map(|val| val.to_vec()))?)
	}

	fn read_value_with<L: TrieConfiguration, Q: Query<L::Hash, Item=DBValue>, DB>(
		&self, db: &DB, root_slice: &[u8], key: &[u8], query: Q
	) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>
	{
		let mut root = TrieHash::<L>::default();
		// root is fetched from DB, not writable by runtime, so it's always valid.
		root.as_mut().copy_from_slice(root_slice);

		Ok(TrieDB::<L>::new(&*db, &root)?.get_with(key, query).map(|x| x.map(|val| val.to_vec()))?)
	}
}
