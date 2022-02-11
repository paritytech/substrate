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

use jsonrpc_core::{Error, ErrorCode, Result};
use jsonrpc_derive::rpc;
use serde::{Deserialize, Serialize};
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use std::sync::Arc;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct MigrationStatusResult {
	top_remaining_to_migrate: u64,
	child_remaining_to_migrate: u64,
}

/// Migration RPC methods.
#[rpc]
pub trait StateMigrationApi<BlockHash> {
	/// Check current migration state.
	///
	/// This call is performed locally without submitting any transactions. Thus executing this
	/// won't change any state. Nonetheless it is a VERY costy call that should be
	/// only exposed to trusted peers.
	#[rpc(name = "state-trie-migration-status")]
	fn call(&self, at: Option<BlockHash>) -> Result<MigrationStatusResult>;
}

/// An implementation of state migration specific RPC methods.
pub struct MigrationRpc<C, B, BA> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<(B, BA)>,
}

impl<C, B, BA> MigrationRpc<C, B, BA> {
	/// Create new state migration rpc for the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		MigrationRpc { client, _marker: Default::default() }
	}
}

impl<C, B, BA> StateMigrationApi<<B as BlockT>::Hash> for MigrationRpc<C, B, BA>
where
	B: BlockT,
	C: Send
		+ Sync
		+ 'static
		+ sc_client_api::StorageProvider<B, BA>
		+ sc_client_api::HeaderBackend<B>,
	BA: 'static + sc_client_api::backend::Backend<B>,
{
	fn call(&self, at: Option<<B as BlockT>::Hash>) -> Result<MigrationStatusResult> {
		let block_id = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));
		let (top, child) =
			self.client.state_migration_status(&block_id).map_err(error_into_rpc_err)?;
		Ok(MigrationStatusResult {
			top_remaining_to_migrate: top,
			child_remaining_to_migrate: child,
		})
	}
}

fn error_into_rpc_err(err: impl std::fmt::Display) -> Error {
	Error {
		code: ErrorCode::ServerError(0), // TODO check errors code
		message: "Error while checking migration state".into(),
		data: Some(err.to_string().into()),
	}
}
