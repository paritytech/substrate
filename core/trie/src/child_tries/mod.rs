//! Child trie declarations.

mod default;

pub use self::default::DefaultChildTrie;

use crate::{TrieHash, TrieError};
use trie_db::{TrieConfiguration, DBValue, Query};
use hash_db::{HashDB, HashDBRef, PlainDB, PlainDBRef};

/// Definition for a child trie.
pub trait ChildTrie {
	/// Default root of the child trie.
	fn default_root<L: TrieConfiguration>(&self) -> Vec<u8>;

	/// Given its ordered contents, closed form, calculate a child trie's root.
	fn root<L: TrieConfiguration, I, A, B>(&self, input: I) -> Vec<u8> where
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>;

	/// Given delta values, calculate the updated child trie root.
	fn delta_root<L: TrieConfiguration, I, A, B, DB>(
		&self, db: &mut DB, root_vec: Vec<u8>, delta: I
	) -> Result<Vec<u8>, Box<TrieError<L>>> where
		I: IntoIterator<Item = (A, Option<B>)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
		DB: HashDB<L::Hash, DBValue> + PlainDB<TrieHash<L>, DBValue>;

	/// Call `f` for all keys in a child trie.
	fn for_keys<L: TrieConfiguration, F: FnMut(&[u8]), DB>(
		&self, db: &DB, root_slice: &[u8], f: F
	) -> Result<(), Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>;

	/// Read a value from the child trie.
	fn read_value<L: TrieConfiguration, DB>(
		&self, db: &DB, root_slice: &[u8], key: &[u8]
	) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>;

	/// Read a value from the child trie with given query.
	fn read_value_with<L: TrieConfiguration, Q: Query<L::Hash, Item=DBValue>, DB>(
		&self, db: &DB, root_slice: &[u8], key: &[u8], query: Q
	) -> Result<Option<Vec<u8>>, Box<TrieError<L>>> where
		DB: HashDBRef<L::Hash, DBValue> + PlainDBRef<TrieHash<L>, DBValue>;
}
