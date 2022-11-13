// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Rpc for state migration.

use jsonrpsee::{
	core::{Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	types::error::{CallError, ErrorCode, ErrorObject},
};
use sc_rpc_api::DenyUnsafe;
use serde::{Deserialize, Serialize};
use sp_runtime::traits::Block as BlockT;
use std::sync::Arc;

use sp_core::{
	storage::{ChildInfo, ChildType, PrefixedStorageKey},
	Hasher,
};
use sp_state_machine::backend::AsTrieBackend;
use sp_trie::{
	trie_types::{TrieDB, TrieDBBuilder},
	KeySpacedDB, Trie,
};
use trie_db::{
	node::{NodePlan, ValuePlan},
	TrieDBNodeIterator,
};

fn count_migrate<'a, H: Hasher>(
	storage: &'a dyn trie_db::HashDBRef<H, Vec<u8>>,
	root: &'a H::Out,
) -> std::result::Result<(u64, TrieDB<'a, 'a, H>), String> {
	let mut nb = 0u64;
	let trie = TrieDBBuilder::new(storage, root).build();
	let iter_node =
		TrieDBNodeIterator::new(&trie).map_err(|e| format!("TrieDB node iterator error: {}", e))?;
	for node in iter_node {
		let node = node.map_err(|e| format!("TrieDB node iterator error: {}", e))?;
		match node.2.node_plan() {
			NodePlan::Leaf { value, .. } | NodePlan::NibbledBranch { value: Some(value), .. } =>
				if let ValuePlan::Inline(range) = value {
					if (range.end - range.start) as u32 >=
						sp_core::storage::TRIE_VALUE_NODE_THRESHOLD
					{
						nb += 1;
					}
				},
			_ => (),
		}
	}
	Ok((nb, trie))
}

/// Check trie migration status.
pub fn migration_status<H, B>(backend: &B) -> std::result::Result<(u64, u64), String>
where
	H: Hasher,
	H::Out: codec::Codec,
	B: AsTrieBackend<H>,
{
	let trie_backend = backend.as_trie_backend();
	let essence = trie_backend.essence();
	let (nb_to_migrate, trie) = count_migrate(essence, essence.root())?;

	let mut nb_to_migrate_child = 0;
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
		nb_to_migrate_child += count_migrate(&storage, &child_root)?.0;
	}

	Ok((nb_to_migrate, nb_to_migrate_child))
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct MigrationStatusResult {
	top_remaining_to_migrate: u64,
	child_remaining_to_migrate: u64,
}

/// Migration RPC methods.
#[rpc(server)]
pub trait StateMigrationApi<BlockHash> {
	/// Check current migration state.
	///
	/// This call is performed locally without submitting any transactions. Thus executing this
	/// won't change any state. Nonetheless it is a VERY costy call that should be
	/// only exposed to trusted peers.
	#[method(name = "state_trieMigrationStatus")]
	fn call(&self, at: Option<BlockHash>) -> RpcResult<MigrationStatusResult>;
}

/// An implementation of state migration specific RPC methods.
pub struct StateMigration<C, B, BA> {
	client: Arc<C>,
	backend: Arc<BA>,
	deny_unsafe: DenyUnsafe,
	_marker: std::marker::PhantomData<(B, BA)>,
}

impl<C, B, BA> StateMigration<C, B, BA> {
	/// Create new state migration rpc for the given reference to the client.
	pub fn new(client: Arc<C>, backend: Arc<BA>, deny_unsafe: DenyUnsafe) -> Self {
		StateMigration { client, backend, deny_unsafe, _marker: Default::default() }
	}
}

impl<C, B, BA> StateMigrationApiServer<<B as BlockT>::Hash> for StateMigration<C, B, BA>
where
	B: BlockT,
	C: Send + Sync + 'static + sc_client_api::HeaderBackend<B>,
	BA: 'static + sc_client_api::backend::Backend<B>,
{
	fn call(&self, at: Option<<B as BlockT>::Hash>) -> RpcResult<MigrationStatusResult> {
		self.deny_unsafe.check_if_safe()?;

		let hash = at.unwrap_or_else(|| self.client.info().best_hash);
		let state = self.backend.state_at(hash).map_err(error_into_rpc_err)?;
		let (top, child) = migration_status(&state).map_err(error_into_rpc_err)?;

		Ok(MigrationStatusResult {
			top_remaining_to_migrate: top,
			child_remaining_to_migrate: child,
		})
	}
}

fn error_into_rpc_err(err: impl std::fmt::Display) -> JsonRpseeError {
	JsonRpseeError::Call(CallError::Custom(ErrorObject::owned(
		ErrorCode::InternalError.code(),
		"Error while checking migration state",
		Some(err.to_string()),
	)))
}
