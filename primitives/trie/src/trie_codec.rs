// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use crate::{CompactProof, HashDBT, StorageProof, TrieConfiguration, TrieHash, EMPTY_PREFIX};
use sp_core::storage::{well_known_keys, ChildType, PrefixedStorageKey};
use sp_std::{boxed::Box, vec, vec::Vec};
use trie_db::{CError, Trie};

/// Error for trie node decoding.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<H, CodecError> {
	#[cfg_attr(feature = "std", error("Invalid root {0:x?}, expected {1:x?}"))]
	RootMismatch(H, H),
	#[cfg_attr(feature = "std", error("Missing nodes in the proof"))]
	IncompleteProof,
	#[cfg_attr(feature = "std", error("Child node content with no root in proof"))]
	ExtraneousChildNode,
	#[cfg_attr(feature = "std", error("Proof of child trie {0:x?} not in parent proof"))]
	ExtraneousChildProof(H),
	#[cfg_attr(feature = "std", error("Invalid root {0:x?}, expected {1:x?}"))]
	InvalidChildRoot(Vec<u8>, Vec<u8>),
	#[cfg_attr(feature = "std", error("Trie error: {0:?}"))]
	TrieError(Box<trie_db::TrieError<H, CodecError>>),
	#[cfg_attr(feature = "std", error("Parent sized trie error: {0:?}"))]
	ParentSizedChildTrieError(Box<trie_db::TrieError<H, crate::error::Error>>),
	#[cfg_attr(feature = "std", error("Mmr child state error: {0:?}"))]
	MmrChildError(&'static str),
}

impl<H, CodecError> From<Box<trie_db::TrieError<H, CodecError>>> for Error<H, CodecError> {
	fn from(error: Box<trie_db::TrieError<H, CodecError>>) -> Self {
		Error::TrieError(error)
	}
}

/// Decode a compact proof.
///
/// Takes as input a destination `db` for decoded node and `encoded`
/// an iterator of compact encoded nodes.
///
/// Child trie are decoded in order of child trie root present
/// in the top trie.
pub fn decode_compact<'a, L, DB, I>(
	db: &mut DB,
	encoded: I,
	expected_root: Option<&TrieHash<L>>,
) -> Result<TrieHash<L>, Error<TrieHash<L>, CError<L>>>
where
	L: TrieConfiguration,
	DB: HashDBT<L::Hash, trie_db::DBValue> + hash_db::HashDBRef<L::Hash, trie_db::DBValue>,
	I: IntoIterator<Item = &'a [u8]>,
{
	let mut nodes_iter = encoded.into_iter();
	let (top_root, _nb_used) = trie_db::decode_compact_from_iter::<L, _, _>(db, &mut nodes_iter)?;

	// Only check root if expected root is passed as argument.
	if let Some(expected_root) = expected_root {
		if expected_root != &top_root {
			return Err(Error::RootMismatch(top_root, *expected_root))
		}
	}

	let mut child_tries = Vec::new();
	let mut mmrs = Vec::new();
	{
		// fetch child trie roots
		let trie = crate::TrieDB::<L>::new(db, &top_root);

		let mut iter = trie.iter()?;

		let childtrie_roots = well_known_keys::CHILD_STORAGE_KEY_PREFIX;
		if iter.seek(childtrie_roots).is_ok() {
			loop {
				match iter.next() {
					Some(Ok((key, value))) => {
						let prefixed_key = PrefixedStorageKey::new_ref(&key);
						match ChildType::from_prefixed_key(prefixed_key) {
							Some((ChildType::Mmr, _unprefixed)) => {
								let mut root = TrieHash::<L>::default();
								// still in a proof so prevent panic
								if root.as_mut().len() + 8 != value.as_slice().len() {
									return Err(Error::InvalidChildRoot(key, value))
								}
								root.as_mut().copy_from_slice(&value[8..]);
								let mut nb_encoded = [0u8; 8];
								nb_encoded.copy_from_slice(&value[..8]);
								let nb_elt = u64::from_le_bytes(nb_encoded);
								mmrs.push((root, nb_elt));
							},
							Some((child_type, _unprefixed)) => {
								// we expect all default child trie root to be correctly encoded.
								// see other child trie functions.
								let mut root = TrieHash::<L>::default();
								// still in a proof so prevent panic
								if root.as_mut().len() != value.as_slice().len() {
									return Err(Error::InvalidChildRoot(key, value))
								}
								root.as_mut().copy_from_slice(value.as_ref());
								child_tries.push((root, child_type));
							},
							None => break,
						}
					},
					// allow incomplete database error: we only
					// require access to data in the proof.
					Some(Err(error)) => match *error {
						trie_db::TrieError::IncompleteDatabase(..) => (),
						e => return Err(Box::new(e).into()),
					},
					None => break,
				}
			}
		}
	}

	if !HashDBT::<L::Hash, _>::contains(db, &top_root, EMPTY_PREFIX) {
		return Err(Error::IncompleteProof)
	}

	let mut previous_extracted_child_trie = None;
	let mut nodes_iter = nodes_iter.peekable();
	let mut last_child_type = None;
	let mut skip_till_new_type = false;
	for (child_root, child_type) in child_tries.into_iter() {
		let peek = nodes_iter.peek();
		// child trie are not allowed to encode their root/first node
		// to [trie_constants::ESCAPE_COMPACT_HEADER], otherwhise
		// please escape it.
		// TODO implement escape? : if double ESCAPE_COMPACT_HEADER
		// at start, remove first.
		if peek == Some(&&[crate::trie_constants::ESCAPE_COMPACT_HEADER][..]) {
			skip_till_new_type = true;
		}
		if skip_till_new_type && last_child_type == Some(child_type) {
			continue
		}
		skip_till_new_type = false;
		last_child_type = Some(child_type);
		if previous_extracted_child_trie.is_none() && peek.is_some() {
			match child_type {
				ChildType::ParentKeyId => {
					let (top_root, _) =
						trie_db::decode_compact_from_iter::<L, _, _>(db, &mut nodes_iter)?;
					previous_extracted_child_trie = Some(top_root);
				},
				ChildType::ParentSized => {
					let (top_root, _) = trie_db::decode_compact_from_iter::<
						crate::LayoutParentSized<L::Hash>,
						_,
						_,
					>(db, &mut nodes_iter)
					.map_err(|e| Error::ParentSizedChildTrieError(e))?;
					previous_extracted_child_trie = Some(top_root);
				},
				ChildType::Mmr => unreachable!("in mmrs"),
			}
		}

		// we do not early exit on root mismatch but try the
		// other read from proof (some child root may be
		// in proof without actual child content).
		// TODO this is not true anymore as we cannot mistake a child type.
		// -> Should change code to not allow it.
		if Some(child_root) == previous_extracted_child_trie {
			previous_extracted_child_trie = None;
		}
	}

	for (mmr_root, nb_elt) in mmrs.into_iter() {
		if previous_extracted_child_trie.is_none() && nodes_iter.peek().is_some() {
			previous_extracted_child_trie = Some(
				crate::mmr::MmrDBMut::decode_compact(db, nb_elt, &mut nodes_iter)
					.map_err(Error::MmrChildError)?,
			);
		}

		// we do not early exit on root mismatch but try the
		// other read from proof (some child root may be
		// in proof without actual child content).
		if Some(mmr_root) == previous_extracted_child_trie {
			previous_extracted_child_trie = None;
		}
	}

	if let Some(child_root) = previous_extracted_child_trie {
		// A child root was read from proof but is not present
		// in top trie.
		return Err(Error::ExtraneousChildProof(child_root))
	}

	if nodes_iter.next().is_some() {
		return Err(Error::ExtraneousChildNode)
	}

	Ok(top_root)
}

/// Encode a compact proof.
///
/// Takes as input all full encoded node from the proof, and
/// the root.
/// Then parse all child trie root and compress main trie content first
/// then all child trie contents.
/// Child trie are ordered by the order of their roots in the top trie.
pub fn encode_compact<L>(
	proof: StorageProof,
	root: TrieHash<L>,
) -> Result<CompactProof, Error<TrieHash<L>, CError<L>>>
where
	L: TrieConfiguration,
{
	let mut child_tries = Vec::new();
	let mut mmrs = Vec::new();
	let mut partial_db = proof.into_memory_db();
	let mut compact_proof = {
		let trie = crate::TrieDB::<L>::new(&partial_db, &root);

		let mut iter = trie.iter()?;

		let childtrie_roots = well_known_keys::CHILD_STORAGE_KEY_PREFIX;
		if iter.seek(childtrie_roots).is_ok() {
			loop {
				match iter.next() {
					Some(Ok((key, value))) => {
						let prefixed_key = PrefixedStorageKey::new_ref(&key);
						match ChildType::from_prefixed_key(prefixed_key) {
							Some((ChildType::Mmr, _unprefixed)) => {
								let mut root = TrieHash::<L>::default();
								if root.as_mut().len() + 8 != value.as_slice().len() {
									return Err(Error::InvalidChildRoot(
										key.to_vec(),
										value.to_vec(),
									))
								}
								root.as_mut().copy_from_slice(&value[8..]);
								let mut nb_encoded = [0u8; 8];
								nb_encoded.copy_from_slice(&value[..8]);
								let nb_elt = u64::from_le_bytes(nb_encoded);
								mmrs.push((root, nb_elt));
							},
							Some((child_type, _unprefixed)) => {
								let mut root = TrieHash::<L>::default();
								if root.as_mut().len() != value.as_slice().len() {
									// some child trie root in top trie are not an encoded hash.
									return Err(Error::InvalidChildRoot(
										key.to_vec(),
										value.to_vec(),
									))
								}
								root.as_mut().copy_from_slice(value.as_ref());
								child_tries.push((root, child_type));
							},
							None => break,
						}
					},
					// allow incomplete database error: we only
					// require access to data in the proof.
					Some(Err(error)) => match *error {
						trie_db::TrieError::IncompleteDatabase(..) => (),
						e => return Err(Box::new(e).into()),
					},
					_ => break,
				}
			}
		}

		trie_db::encode_compact::<L>(&trie)?
	};

	let mut last_child = None;
	let mut last_skipped = false;
	for (child_root, child_type) in child_tries {
		if last_skipped && Some(child_type) != last_child {
			compact_proof.push(vec![crate::trie_constants::ESCAPE_COMPACT_HEADER]);
		}
		last_child = Some(child_type);
		if !HashDBT::<L::Hash, _>::contains(&partial_db, &child_root, EMPTY_PREFIX) {
			// child proof are allowed to be missing (unused root can be included
			// due to trie structure modification).
			last_skipped = true;
			continue
		}
		last_skipped = false;

		match child_type {
			ChildType::ParentKeyId => {
				let trie = crate::TrieDB::<L>::new(&partial_db, &child_root);
				let child_proof = trie_db::encode_compact::<L>(&trie)?;

				compact_proof.extend(child_proof);
			},
			ChildType::ParentSized => {
				let trie = crate::TrieDB::<crate::LayoutParentSized<L::Hash>>::new(
					&partial_db,
					&child_root,
				);
				let child_proof =
					trie_db::encode_compact::<crate::LayoutParentSized<L::Hash>>(&trie)
						.map_err(|e| Error::ParentSizedChildTrieError(e))?;

				compact_proof.extend(child_proof);
			},
			ChildType::Mmr => unreachable!("in mmrs"),
		}
	}
	for (mut mmr_root, number_element) in mmrs {
		if !HashDBT::<L::Hash, _>::contains(&partial_db, &mmr_root, EMPTY_PREFIX) {
			// just skip
			continue
		}
		let mmr = crate::mmr::MmrDBMut {
			peaks: Default::default(),
			db: &mut partial_db,
			root: &mut mmr_root,
			number_element,
		};
		let child_proof = mmr.encode_compact().map_err(|e| Error::MmrChildError(e))?;
		compact_proof.extend(child_proof);
	}

	Ok(CompactProof { encoded_nodes: compact_proof })
}
