// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
//! the [`SyncState`] will fail at instantiation.

#![deny(unused_crate_dependencies)]

use jsonrpsee::{
	core::{Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	types::{error::CallError, ErrorObject},
};
use sc_client_api::StorageData;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::sync::Arc;

type SharedAuthoritySet<TBl> =
	sc_consensus_grandpa::SharedAuthoritySet<<TBl as BlockT>::Hash, NumberFor<TBl>>;
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

	#[error("JsonRpc error: {0}")]
	JsonRpc(String),

	#[error(
		"The light sync state extension is not provided by the chain spec. \
		Read the `sc-sync-state-rpc` crate docs on how to do this!"
	)]
	LightSyncStateExtensionNotFound,
}

impl<Block: BlockT> From<Error<Block>> for JsonRpseeError {
	fn from(error: Error<Block>) -> Self {
		let message = match error {
			Error::JsonRpc(s) => s,
			_ => error.to_string(),
		};
		CallError::Custom(ErrorObject::owned(1, message, None::<()>)).into()
	}
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

/// Hardcoded information that allows light clients to sync quickly.
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
		sc_consensus_grandpa::AuthoritySet<<Block as BlockT>::Hash, NumberFor<Block>>,
}

/// An api for sync state RPC calls.
#[rpc(client, server)]
pub trait SyncStateApi {
	/// Returns the JSON serialized chainspec running the node, with a sync state.
	#[method(name = "sync_state_genSyncSpec")]
	fn system_gen_sync_spec(&self, raw: bool) -> RpcResult<serde_json::Value>;
}

/// An api for sync state RPC calls.
pub struct SyncState<Block: BlockT, Client> {
	chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
	client: Arc<Client>,
	shared_authority_set: SharedAuthoritySet<Block>,
	shared_epoch_changes: SharedEpochChanges<Block>,
}

impl<Block, Client> SyncState<Block, Client>
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
	) -> Result<Self, Error<Block>> {
		if sc_chain_spec::get_extension::<LightSyncStateExtension>(chain_spec.extensions())
			.is_some()
		{
			Ok(Self { chain_spec, client, shared_authority_set, shared_epoch_changes })
		} else {
			Err(Error::<Block>::LightSyncStateExtensionNotFound)
		}
	}

	fn build_sync_state(&self) -> Result<LightSyncState<Block>, Error<Block>> {
		let finalized_hash = self.client.info().finalized_hash;
		let finalized_header = self
			.client
			.header(finalized_hash)?
			.ok_or_else(|| sp_blockchain::Error::MissingHeader(finalized_hash.to_string()))?;

		let finalized_block_weight =
			sc_consensus_babe::aux_schema::load_block_weight(&*self.client, finalized_hash)?
				.ok_or(Error::LoadingBlockWeightFailed(finalized_hash))?;

		Ok(LightSyncState {
			finalized_block_header: finalized_header,
			babe_epoch_changes: self.shared_epoch_changes.shared_data().clone(),
			babe_finalized_block_weight: finalized_block_weight,
			grandpa_authority_set: self.shared_authority_set.clone_inner(),
		})
	}
}

impl<Block, Backend> SyncStateApiServer for SyncState<Block, Backend>
where
	Block: BlockT,
	Backend: HeaderBackend<Block> + sc_client_api::AuxStore + 'static,
{
	fn system_gen_sync_spec(&self, raw: bool) -> RpcResult<serde_json::Value> {
		let current_sync_state = self.build_sync_state()?;
		let mut chain_spec = self.chain_spec.cloned_box();

		let extension = sc_chain_spec::get_extension_mut::<LightSyncStateExtension>(
			chain_spec.extensions_mut(),
		)
		.ok_or(Error::<Block>::LightSyncStateExtensionNotFound)?;

		let val = serde_json::to_value(&current_sync_state)?;
		*extension = Some(val);

		let json_str = chain_spec.as_json(raw).map_err(|e| Error::<Block>::JsonRpc(e))?;
		serde_json::from_str(&json_str).map_err(Into::into)
	}
}
