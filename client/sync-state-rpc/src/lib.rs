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
//!
//! Currently only usable with BABE + GRANDPA.
//!
//! # Usage
//!
//! To use the light sync state, it needs to be added as an extension to the chain spec:
//!
//! ```
//! use sc_sync_state_rpc::LightSyncStateExtension;
//!
//! #[derive(Default, Clone, serde::Serialize, serde::Deserialize, sc_chain_spec::ChainSpecExtension)]
//! #[serde(rename_all = "camelCase")]
//! pub struct Extensions {
//!    light_sync_state: LightSyncStateExtension,
//! }
//!
//! type ChainSpec = sc_chain_spec::GenericChainSpec<(), Extensions>;
//! ```
//!
//! If the [`LightSyncStateExtension`] is not added as an extension to the chain spec,
//! the [`SyncStateRpcHandler`] will fail at instantiation.

#![deny(unused_crate_dependencies)]

use sc_client_api::StorageData;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
};
use std::sync::Arc;
use jsonrpsee::types::error::{Error as JsonRpseeError, CallError};
use jsonrpsee::RpcModule;

type SharedAuthoritySet<TBl> =
	sc_finality_grandpa::SharedAuthoritySet<<TBl as BlockT>::Hash, NumberFor<TBl>>;
type SharedEpochChanges<TBl> =
	sc_consensus_epochs::SharedEpochChanges<TBl, sc_consensus_babe::Epoch>;

/// Error type used by this crate.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error<Block: BlockT> {
	#[error(transparent)]
	Blockchain(#[from] sp_blockchain::Error),

	#[error("Failed to load the block weight for block {0:?}")]
	LoadingBlockWeightFailed(Block::Hash),

	#[error(
		"The light sync state extension is not provided by the chain spec. \
		Read the `sc-sync-state-rpc` crate docs on how to do this!"
	)]
	LightSyncStateExtensionNotFound,
}

/// Serialize the given `val` by encoding it with SCALE codec and serializing it as hex.
fn serialize_encoded<S: serde::Serializer, T: codec::Encode>(
	val: &T,
	s: S,
) -> Result<S::Ok, S::Error> {
	let encoded = StorageData(val.encode());
	serde::Serialize::serialize(&encoded, s)
}

/// The light sync state extension.
///
/// This represents a JSON serialized [`LightSyncState`]. It is required to be added to the
/// chain-spec as an extension.
pub type LightSyncStateExtension = Option<serde_json::Value>;

/// Hardcoded infomation that allows light clients to sync quickly.
#[derive(serde::Serialize, Clone)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct LightSyncState<Block: BlockT> {
	/// The header of the best finalized block.
	#[serde(serialize_with = "serialize_encoded")]
	pub finalized_block_header: <Block as BlockT>::Header,
	/// The epoch changes tree for babe.
	#[serde(serialize_with = "serialize_encoded")]
	pub babe_epoch_changes: sc_consensus_epochs::EpochChangesFor<Block, sc_consensus_babe::Epoch>,
	/// The babe weight of the finalized block.
	pub babe_finalized_block_weight: sc_consensus_babe::BabeBlockWeight,
	/// The authority set for grandpa.
	#[serde(serialize_with = "serialize_encoded")]
	pub grandpa_authority_set:
		sc_finality_grandpa::AuthoritySet<<Block as BlockT>::Hash, NumberFor<Block>>,
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
	) -> Result<Self, Error<Block>> {
		if sc_chain_spec::get_extension::<LightSyncStateExtension>(chain_spec.extensions())
			.is_some()
		{
			Ok(Self { chain_spec, client, shared_authority_set, shared_epoch_changes, deny_unsafe })
		} else {
			Err(Error::<Block>::LightSyncStateExtensionNotFound)
		}
	}

	/// Convert this [`SyncStateRpc`] to a RPC module.
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut module = RpcModule::new(self);

		// Returns the json-serialized chainspec running the node, with a sync state.
		module.register_method("sync_state_genSyncSpec", |params, sync_state| {
			sync_state.deny_unsafe.check_if_safe()?;

			let raw = params.one()?;
			let current_sync_state = sync_state.build_sync_state().map_err(|e| CallError::Failed(Box::new(e)))?;
			let mut chain_spec = sync_state.chain_spec.cloned_box();

			let extension = sc_chain_spec::get_extension_mut::<LightSyncStateExtension>(
				chain_spec.extensions_mut(),
			)
			.ok_or_else(|| {
				CallError::Failed(anyhow::anyhow!("Could not find `LightSyncState` chain-spec extension!").into())
			})?;

			let val = serde_json::to_value(&current_sync_state).map_err(|e| CallError::Failed(Box::new(e)))?;
			*extension = Some(val);

			chain_spec.as_json(raw).map_err(|e| CallError::Failed(anyhow::anyhow!(e).into()))
		})?;
		Ok(module)
	}

	fn build_sync_state(&self) -> Result<LightSyncState<Block>, Error<Block>> {
		let finalized_hash = self.client.info().finalized_hash;
		let finalized_header = self
			.client
			.header(BlockId::Hash(finalized_hash))?
			.ok_or_else(|| sp_blockchain::Error::MissingHeader(finalized_hash.to_string()))?;

		let finalized_block_weight =
			sc_consensus_babe::aux_schema::load_block_weight(&*self.client, finalized_hash)?
				.ok_or_else(|| Error::LoadingBlockWeightFailed(finalized_hash))?;

		Ok(LightSyncState {
			finalized_block_header: finalized_header,
			babe_epoch_changes: self.shared_epoch_changes.shared_data().clone(),
			babe_finalized_block_weight: finalized_block_weight,
			grandpa_authority_set: self.shared_authority_set.clone_inner(),
		})
	}
}


