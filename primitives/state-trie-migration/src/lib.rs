// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Utilities for trie state migration.

use sp_core::{
	storage::{ChildInfo, ChildType, PrefixedStorageKey},
	Hasher,
};
use sp_state_machine::Backend;
use sp_trie::{KeySpacedDB, Trie};
use trie_db::{
	node::{NodePlan, ValuePlan},
	TrieDBNodeIterator,
};

/// Check trie migration status.
pub fn migration_status<H, B>(backend: &B) -> Result<(u64, u64), String>
where
	H: Hasher,
	H::Out: codec::Codec,
	B: Backend<H>,
{
	let trie_backend = if let Some(backend) = backend.as_trie_backend() {
		backend
	} else {
		return Err("No access to trie from backend.".to_string())
	};
	let essence = trie_backend.essence();

	let threshold: u32 = sp_core::storage::TRIE_VALUE_NODE_THRESHOLD;
	let mut nb_to_migrate = 0;
	let mut nb_to_migrate_child = 0;

	let trie = sp_trie::trie_types::TrieDB::new(essence, &essence.root())
		.map_err(|e| format!("TrieDB creation error: {}", e))?;
	let iter_node =
		TrieDBNodeIterator::new(&trie).map_err(|e| format!("TrieDB node iterator error: {}", e))?;
	for node in iter_node {
		let node = node.map_err(|e| format!("TrieDB node iterator error: {}", e))?;
		match node.2.node_plan() {
			NodePlan::Leaf { value, .. } | NodePlan::NibbledBranch { value: Some(value), .. } =>
				if let ValuePlan::Inline(range) = value {
					if (range.end - range.start) as u32 >= threshold {
						nb_to_migrate += 1;
					}
				},
			_ => (),
		}
	}

	let mut child_roots: Vec<(ChildInfo, Vec<u8>)> = Vec::new();
	// get all child trie roots
	for key_value in trie.iter().map_err(|e| format!("TrieDB node iterator error: {}", e))? {
		let (key, value) = key_value.map_err(|e| format!("TrieDB node iterator error: {}", e))?;
		if key[..].starts_with(sp_core::storage::well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX)
		{
			let prefixed_key = PrefixedStorageKey::new(key);
			let (_type, unprefixed) = ChildType::from_prefixed_key(&prefixed_key).unwrap();
			child_roots.push((ChildInfo::new_default(unprefixed), value));
		}
	}
	for (child_info, root) in child_roots {
		let mut child_root = H::Out::default();
		let storage = KeySpacedDB::new(essence, child_info.keyspace());

		child_root.as_mut()[..].copy_from_slice(&root[..]);
		let trie = sp_trie::trie_types::TrieDB::new(&storage, &child_root)
			.map_err(|e| format!("New child TrieDB error: {}", e))?;
		let iter_node = TrieDBNodeIterator::new(&trie)
			.map_err(|e| format!("TrieDB node iterator error: {}", e))?;
		for node in iter_node {
			let node = node.map_err(|e| format!("Child TrieDB node iterator error: {}", e))?;
			match node.2.node_plan() {
				NodePlan::Leaf { value, .. } |
				NodePlan::NibbledBranch { value: Some(value), .. } =>
					if let ValuePlan::Inline(range) = value {
						if (range.end - range.start) as u32 >= threshold {
							nb_to_migrate_child += 1;
						}
					},
				_ => (),
			}
		}
	}

	Ok((nb_to_migrate, nb_to_migrate_child))
}
