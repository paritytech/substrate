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

//! Compact proof support.
//!
//! This uses compact proof from trie crate and extends
//! it to substrate specific layout and child trie system.

use crate::{EMPTY_PREFIX, HashDBT, LazyFetcher,
	TrieHash, TrieError, TrieConfiguration};

type VerifyError<L> = crate::VerifyError<TrieHash<L>, Box<TrieError<L>>>;

fn verify_error<L: TrieConfiguration>(error: Box<TrieError<L>>) -> VerifyError<L> {
	VerifyError::<L>::DecodeError(error)
}

/// Decode a compact proof.
///
/// Takes as input a destination `db` for decoded node and `encoded`
/// an iterator of compact encoded nodes.
///
/// Also allows optionally injecting specified value in
/// top trie proof with `know_keys` and the lazy
/// associated `fetcher`.
///
/// Child trie are decoded in order of child trie root present
/// in the top trie.
pub fn decode_compact<'a, L, DB, I, F, K>(
	db: &mut DB,
	encoded: I,
	fetcher: F,
	known_keys: Option<K>,
	expected_root: Option<&TrieHash<L>>,
) -> Result<TrieHash<L>, VerifyError<L>>
	where
		L: TrieConfiguration,
		DB: HashDBT<L::Hash, trie_db::DBValue> + hash_db::HashDBRef<L::Hash, trie_db::DBValue>,
		I: IntoIterator<Item = &'a [u8]>,
		F: LazyFetcher<'a>,
		K: IntoIterator<Item = &'a [u8]>,
{
	let mut nodes_iter = encoded.into_iter();
	let (top_root, _nb_used) = if let Some(known_keys) = known_keys {
		trie_db::decode_compact_with_known_values::<L, _, _, _, _, _>(
			db,
			&mut nodes_iter,
			fetcher,
			known_keys,
			false, // current use of compact do to escape empty value.
		).map_err(verify_error::<L>)?
	} else {
		trie_db::decode_compact_from_iter::<L, _, _, _>(
			db,
			&mut nodes_iter,
		).map_err(verify_error::<L>)?
	};

	if let Some(expected_root) = expected_root {
		if expected_root != &top_root {
			return Err(VerifyError::<L>::RootMismatch(expected_root.clone()));
		}
	}

	let mut child_tries = Vec::new();
	{
		// fetch child trie roots
		let trie = crate::TrieDB::<L>::new(db, &top_root).map_err(verify_error::<L>)?;

		use trie_db::Trie;
		let mut iter = trie.iter().map_err(verify_error::<L>)?;

		let childtrie_roots = sp_core::storage::well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX;
		if iter.seek(childtrie_roots).is_ok() {
			loop {
				match iter.next() {
					Some(Ok((key, value))) if key.starts_with(childtrie_roots) => {
						// we expect all default child trie root to be correctly encoded.
						// see other child trie functions.
						let mut root = TrieHash::<L>::default();
						// still in a proof so prevent panic
						if root.as_mut().len() != value.as_slice().len() {
							return Err(VerifyError::<L>::RootMismatch(Default::default()));
						}
						root.as_mut().copy_from_slice(value.as_ref());
						child_tries.push(root);
					},
					// allow incomplete database error: we only
					// require access to data in the proof.
					Some(Err(error)) => match *error {
						trie_db::TrieError::IncompleteDatabase(..) => (),
						e => panic!("{:?}", e),
					},
					_ => break,
				}
			}
		}
	}

	if !HashDBT::<L::Hash, _>::contains(db, &top_root, EMPTY_PREFIX) {
		return Err(VerifyError::<L>::IncompleteProof);
	}

	for child_root in child_tries.into_iter() {
		if !HashDBT::<L::Hash, _>::contains(db, &child_root, EMPTY_PREFIX) {
			// child proof are allowed to be missing (unused root can be included
			// due to trie structure modification).
			continue;
		}

		let (top_root, _nb_used) = trie_db::decode_compact_from_iter::<L, _, _, _>(
			db,
			&mut nodes_iter,
		).map_err(verify_error::<L>)?;

		if child_root != top_root {
			return Err(VerifyError::<L>::RootMismatch(child_root));
		}
	}

	if nodes_iter.next().is_some() {
		return Err(VerifyError::<L>::ExtraneousNode);
	}

	Ok(top_root)
}
