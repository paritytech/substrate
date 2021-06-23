// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! A RPC handler to create sync states for light clients.
//! Currently only usable with BABE + GRANDPA.

#![deny(unused_crate_dependencies)]

use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_blockchain::HeaderBackend;
use std::sync::Arc;
use sp_runtime::generic::BlockId;
use jsonrpsee_types::error::Error as JsonRpseeError;
use jsonrpsee::RpcModule;

use jsonrpc_derive::rpc;

type SharedAuthoritySet<TBl> =
	sc_finality_grandpa::SharedAuthoritySet<<TBl as BlockT>::Hash, NumberFor<TBl>>;
type SharedEpochChanges<TBl> = sc_consensus_epochs::SharedEpochChanges<TBl, sc_consensus_babe::Epoch>;

#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
enum Error<Block: BlockT> {
	#[error(transparent)]
	Blockchain(#[from] sp_blockchain::Error),

	#[error("Failed to load the block weight for block {0:?}")]
	LoadingBlockWeightFailed(<Block as BlockT>::Hash),

	// TODO: (dp) remove
	#[error("JsonRpc error: {0}")]
	JsonRpc(String),
}

// TODO: (dp) remove
impl<Block: BlockT> From<Error<Block>> for jsonrpc_core::Error {
	fn from(error: Error<Block>) -> Self {
		let message = match error {
			Error::JsonRpc(s) => s,
			_ => error.to_string(),
		};
		jsonrpc_core::Error {
			message,
			code:  jsonrpc_core::ErrorCode::ServerError(1),
			data: None,
		}
	}
}

// TODO: (dp) we should re-export CallError from the `jsonrpsee` façade crate. And maybe add a `From` impl for `serde_json::Error` as well?
impl<Block: BlockT> From<Error<Block>> for jsonrpsee::types::error::CallError {
	fn from(error: Error<Block>) -> Self {
		Self::Failed(Box::new(error))
	}
}

// TODO: (dp) `sc_chain_spec::ChainSpec::as_json` returns `Result<String, String>` which is super annoying to work with
// (our CallError doesn't have something that can take a String, which is good imo) but seems to be done on purpose, so
// not going to mess with it. This here is a super-hack though and if we do need it, it has to be moved somewhere where
// it makes sense.
/// Wraps an owned `String` and implements the `Error` trait for it.
#[derive(Debug)]
struct StringError {
    error: String
}

impl std::error::Error for StringError {
    fn description(&self) -> &str {
        &self.error
    }
}

impl std::fmt::Display for StringError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Error: {}", self.error)
    }
}

/// An api for sync state RPC calls.
pub struct SyncStateRpc<Block: BlockT, Client> {
	chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
	client: Arc<Client>,
	shared_authority_set: SharedAuthoritySet<Block>,
	shared_epoch_changes: SharedEpochChanges<Block>,
	deny_unsafe: sc_rpc_api::DenyUnsafe,
}

impl<Block, Client> SyncStateRpc<Block, Client>
where
	Block: BlockT,
	Client: HeaderBackend<Block> + sc_client_api::AuxStore + 'static,
{
	/// Create a new sync state RPC helper.
	pub fn new(
		chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
		client: Arc<Client>,
		shared_authority_set: SharedAuthoritySet<Block>,
		shared_epoch_changes: SharedEpochChanges<Block>,
		deny_unsafe: sc_rpc_api::DenyUnsafe,
	) -> Self {
		Self {
			chain_spec, client, shared_authority_set, shared_epoch_changes, deny_unsafe,
		}
	}

	/// Convert this [`SyncStateRpc`] to a RPC module.
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut module = RpcModule::new(self);

		// Returns the json-serialized chainspec running the node, with a sync state.
		module.register_method::<jsonrpsee::types::JsonValue, _>("sync_state_genSyncSpec", |params, sync_state| {
			sync_state.deny_unsafe.check_if_safe()?;

			let raw = params.one()?;
			let mut chain_spec = sync_state.chain_spec.cloned_box();
			let current_sync_state = sync_state.build_sync_state()?;
			chain_spec.set_light_sync_state(current_sync_state.to_serializable());
			let string = chain_spec.as_json(raw).map_err(|error| {
				let string_err = StringError { error };
				jsonrpsee::types::error::CallError::Failed(Box::new(string_err))
			})?;

			serde_json::from_str(&string).map_err(|json_err| jsonrpsee::types::error::CallError::Failed(Box::new(json_err)))
		})?;
		Ok(module)
	}

	fn build_sync_state(&self) -> Result<sc_chain_spec::LightSyncState<Block>, Error<Block>> {
		let finalized_hash = self.client.info().finalized_hash;
		let finalized_header = self.client.header(BlockId::Hash(finalized_hash))?
			.ok_or_else(|| sp_blockchain::Error::MissingHeader(finalized_hash.to_string()))?;

		let finalized_block_weight = sc_consensus_babe::aux_schema::load_block_weight(
				&*self.client,
				finalized_hash,
			)?
			.ok_or_else(|| Error::LoadingBlockWeightFailed(finalized_hash))?;

		Ok(sc_chain_spec::LightSyncState {
			finalized_block_header: finalized_header,
			babe_epoch_changes: self.shared_epoch_changes.shared_data().clone(),
			babe_finalized_block_weight: finalized_block_weight,
			grandpa_authority_set: self.shared_authority_set.clone_inner(),
		})
	}
}

/// An api for sync state RPC calls.
#[rpc]
pub trait SyncStateRpcApiRemoveMe {
	/// Returns the json-serialized chainspec running the node, with a sync state.
	#[rpc(name = "sync_state_genSyncSpec", returns = "jsonrpc_core::Value")]
	fn system_gen_sync_spec(&self, raw: bool)
		-> jsonrpc_core::Result<jsonrpc_core::Value>;
}

/// The handler for sync state RPC calls.
pub struct SyncStateRpcHandlerRemoveMe<TBl: BlockT, TCl> {
	chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
	client: Arc<TCl>,
	shared_authority_set: SharedAuthoritySet<TBl>,
	shared_epoch_changes: SharedEpochChanges<TBl>,
	deny_unsafe: sc_rpc_api::DenyUnsafe,
}

impl<TBl, TCl> SyncStateRpcHandlerRemoveMe<TBl, TCl>
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl> + sc_client_api::AuxStore + 'static,
{
	/// Create a new handler.
	pub fn new(
		chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
		client: Arc<TCl>,
		shared_authority_set: SharedAuthoritySet<TBl>,
		shared_epoch_changes: SharedEpochChanges<TBl>,
		deny_unsafe: sc_rpc_api::DenyUnsafe,
	) -> Self {
		Self {
			chain_spec, client, shared_authority_set, shared_epoch_changes, deny_unsafe,
		}
	}

	fn build_sync_state(&self) -> Result<sc_chain_spec::LightSyncState<TBl>, Error<TBl>> {
		let finalized_hash = self.client.info().finalized_hash;
		let finalized_header = self.client.header(BlockId::Hash(finalized_hash))?
			.ok_or_else(|| sp_blockchain::Error::MissingHeader(finalized_hash.to_string()))?;

		let finalized_block_weight = sc_consensus_babe::aux_schema::load_block_weight(
				&*self.client,
				finalized_hash,
			)?
			.ok_or_else(|| Error::LoadingBlockWeightFailed(finalized_hash))?;

		Ok(sc_chain_spec::LightSyncState {
			finalized_block_header: finalized_header,
			babe_epoch_changes: self.shared_epoch_changes.shared_data().clone(),
			babe_finalized_block_weight: finalized_block_weight,
			grandpa_authority_set: self.shared_authority_set.clone_inner(),
		})
	}
}

impl<TBl, TCl> SyncStateRpcApiRemoveMe for SyncStateRpcHandlerRemoveMe<TBl, TCl>
	where
		TBl: BlockT,
		TCl: HeaderBackend<TBl> + sc_client_api::AuxStore + 'static,
{
	fn system_gen_sync_spec(&self, raw: bool)
		-> jsonrpc_core::Result<jsonrpc_core::Value>
	{
		if let Err(err) = self.deny_unsafe.check_if_safe() {
			return Err(err.into());
		}

		let mut chain_spec = self.chain_spec.cloned_box();

		let sync_state = self.build_sync_state()
			.map_err(map_error::<TBl,Error<TBl>>)?;

		chain_spec.set_light_sync_state(sync_state.to_serializable());
		let string = chain_spec.as_json(raw).map_err(map_error::<TBl,_>)?;

		serde_json::from_str(&string).map_err(|err| map_error::<TBl,_>(err))
	}
}

// TODO: (dp) remove
fn map_error<Block: BlockT, S: ToString>(error: S) -> jsonrpc_core::Error {
	Error::<Block>::JsonRpc(error.to_string()).into()
}
