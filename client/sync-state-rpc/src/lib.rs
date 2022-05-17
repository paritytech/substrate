// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
//! the [`SyncStateRpc`] will fail at instantiation.

#![deny(unused_crate_dependencies)]

use jsonrpsee::{
	core::{Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	types::{error::CallError, ErrorObject},
};
use sc_client_api::StorageData;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
};

use std::sync::Arc;

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
		sc_finality_grandpa::AuthoritySet<<Block as BlockT>::Hash, NumberFor<Block>>,
}

/// An api for sync state RPC calls.
#[rpc(client, server)]
pub trait SyncStateRpcApi {
	/// Returns the JSON serialized chainspec running the node, with a sync state.
	#[method(name = "sync_state_genSyncSpec")]
	fn system_gen_sync_spec(&self, raw: bool) -> RpcResult<serde_json::Value>;
}

/// An api for sync state RPC calls.
pub struct SyncStateRpc<Block: BlockT, Client>
{
	chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
	client: Arc<Client>,
	shared_authority_set: SharedAuthoritySet<Block>,
	shared_epoch_changes: SharedEpochChanges<Block>,
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
			.header(BlockId::Hash(finalized_hash))?
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

impl<Block, Backend> SyncStateRpcApiServer for SyncStateRpc<Block, Backend>
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

#[cfg(test)]
mod tests {
	use super::*;

	use std::sync::Arc;

	use codec::Decode;
	use sc_block_builder::BlockBuilderProvider;
	use sc_client_api::BlockchainEvents;
	use sc_consensus_babe::Epoch as BabeEpoch;
	use sc_consensus_epochs::EpochChangesFor;
	use sc_finality_grandpa::AuthoritySet;
	use serde::{Deserialize, Serialize};
	use sp_runtime::{traits::Block as BlockT, BuildStorage, Storage};
	use substrate_test_runtime_client::{
		prelude::*,
		runtime::{Block, BlockNumber, Hash, Transfer},
		sp_consensus::BlockOrigin,
	};

	// TODO: better mock of `SharedAuthoritySet` how?!.
	fn empty_authority_set() -> SharedAuthoritySet<Block> {
		let authority_set: AuthoritySet<Hash, BlockNumber> =
			Decode::decode(&mut [0_u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].as_slice()).unwrap();
		authority_set.into()
	}

	// TODO: better mock of `SharedEpochChange` how?!.
	fn empty_epoch() -> SharedEpochChanges<Block> {
		let changes: EpochChangesFor<Block, BabeEpoch> =
			Decode::decode(&mut [0_u8, 0, 0, 0].as_slice()).unwrap();

		SharedEpochChanges::<Block>::new(changes)
	}

	#[derive(Debug, Serialize, Deserialize)]
	struct Genesis(std::collections::BTreeMap<String, String>);

	impl BuildStorage for Genesis {
		fn assimilate_storage(&self, storage: &mut Storage) -> Result<(), String> {
			storage.top.extend(
				self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes())),
			);
			Ok(())
		}
	}

	#[derive(Default, Clone, Serialize, Deserialize, sc_chain_spec::ChainSpecExtension)]
	#[serde(rename_all = "camelCase")]
	pub struct Extensions {
		/// The light sync state extension used by the sync-state rpc.
		pub light_sync_state: LightSyncStateExtension,
	}

	type ChainSpec = sc_chain_spec::GenericChainSpec<Genesis, Extensions>;

	const CHAIN_SPEC: &str = r#"
	{
		"name": "Flaming Fir",
		"id": "flaming-fir",
		"properties": {
			"tokenDecimals": 15,
			"tokenSymbol": "FIR"
		},
		"bootNodes": [
			"/ip4/35.246.224.91/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"
		],
		"telemetryEndpoints": [
			["wss://telemetry.polkadot.io/submit/", 0]
		],
		"protocolId": "fir",
		"genesis": {
			"raw": [
				{
					"0xb2029f8665aac509629f2d28cea790a3": "0x10f26cdb14b5aec7b2789fd5ca80f979cef3761897ae1f37ffb3e154cbcc1c26633919132b851ef0fd2dae42a7e734fe547af5a6b809006100f48944d7fae8e8ef00299981a2b92f878baaf5dbeba5c18d4e70f2a1fcd9c61b32ea18daf38f437800299981a2b92f878baaf5dbeba5c18d4e70f2a1fcd9c61b32ea18daf38f4378547ff0ab649283a7ae01dbc2eb73932eba2fb09075e9485ff369082a2ff38d655633b70b80a6c8bb16270f82cca6d56b27ed7b76c8fd5af2986a25a4788ce440482a3389a6cf42d8ed83888cfd920fec738ea30f97e44699ada7323f08c3380a482a3389a6cf42d8ed83888cfd920fec738ea30f97e44699ada7323f08c3380a68655684472b743e456907b398d3a44c113f189e56d1bbfd55e889e295dfde787932cff431e748892fa48e10c63c17d30f80ca42e4de3921e641249cd7fa3c2f482dbd7297a39fa145c570552249c2ca9dd47e281f0c500c971b59c9dcdcd82e482dbd7297a39fa145c570552249c2ca9dd47e281f0c500c971b59c9dcdcd82e9c7a2ee14e565db0c69f78c7b4cd839fbf52b607d867e9e9c5a79042898a0d129becad03e6dcac03cee07edebca5475314861492cdfc96a2144a67bbe96993326e7e4eb42cbd2e0ab4cae8708ce5509580b8c04d11f6758dbf686d50fe9f91066e7e4eb42cbd2e0ab4cae8708ce5509580b8c04d11f6758dbf686d50fe9f9106"
				},
				{}
			]
		}
	}"#;

	#[tokio::test]
	async fn test_it_works() {
		let mut client = Arc::new(substrate_test_runtime_client::new());

		let mut builder = client.new_block(Default::default()).unwrap();

		builder
			.push_transfer(Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Ferdie.into(),
				amount: 42,
				nonce: 0,
			})
			.unwrap();

		let block = builder.build().unwrap().block;
		let block_hash = block.hash();
		client.import(BlockOrigin::Own, block).await.unwrap();
		client.finalize_block(BlockId::Hash(block_hash), None).unwrap();

		println!("{:?}", client.info().finalized_hash);

		let chain_spec = Box::new(ChainSpec::from_json_bytes(CHAIN_SPEC.as_bytes()).unwrap());

		let serialized_chain_spec: serde_json::Value =
			serde_json::from_str(&chain_spec.as_json(false).unwrap()).unwrap();

		let api = SyncStateRpc::new(chain_spec, client, empty_authority_set(), empty_epoch())
			.unwrap()
			.into_rpc();

		let res: serde_json::Value = api.call("sync_state_genSyncSpec", [false]).await.unwrap();

		assert!(res.get("lightChainSpec").is_some());
	}
}
