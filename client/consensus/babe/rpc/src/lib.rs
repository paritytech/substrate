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

//! RPC api for babe.

use std::{collections::HashMap, sync::Arc};

use futures::TryFutureExt;
use jsonrpsee::{
	core::async_trait,
	proc_macros::rpc,
	types::{ErrorObject, ErrorObjectOwned},
};
use serde::{Deserialize, Serialize};

use sc_consensus_babe::{authorship, BabeWorkerHandle};
use sc_consensus_epochs::Epoch as EpochT;
use sc_rpc_api::{DenyUnsafe, UnsafeRpcError};
use sp_api::ProvideRuntimeApi;
use sp_application_crypto::AppCrypto;
use sp_blockchain::{Error as BlockChainError, HeaderBackend, HeaderMetadata};
use sp_consensus::{Error as ConsensusError, SelectChain};
use sp_consensus_babe::{digests::PreDigest, AuthorityId, BabeApi as BabeRuntimeApi};
use sp_core::crypto::ByteArray;
use sp_keystore::KeystorePtr;
use sp_runtime::traits::{Block as BlockT, Header as _};

const BABE_ERROR: i32 = 9000;

/// Provides rpc methods for interacting with Babe.
#[rpc(client, server)]
pub trait BabeApi {
	/// Returns data about which slots (primary or secondary) can be claimed in the current epoch
	/// with the keys in the keystore.
	#[method(name = "babe_epochAuthorship")]
	async fn epoch_authorship(&self) -> Result<HashMap<AuthorityId, EpochAuthorship>, Error>;
}

/// Provides RPC methods for interacting with Babe.
pub struct Babe<B: BlockT, C, SC> {
	/// shared reference to the client.
	client: Arc<C>,
	/// A handle to the BABE worker for issuing requests.
	babe_worker_handle: BabeWorkerHandle<B>,
	/// shared reference to the Keystore
	keystore: KeystorePtr,
	/// The SelectChain strategy
	select_chain: SC,
	/// Whether to deny unsafe calls
	deny_unsafe: DenyUnsafe,
}

impl<B: BlockT, C, SC> Babe<B, C, SC> {
	/// Creates a new instance of the Babe Rpc handler.
	pub fn new(
		client: Arc<C>,
		babe_worker_handle: BabeWorkerHandle<B>,
		keystore: KeystorePtr,
		select_chain: SC,
		deny_unsafe: DenyUnsafe,
	) -> Self {
		Self { client, babe_worker_handle, keystore, select_chain, deny_unsafe }
	}
}

#[async_trait]
impl<B: BlockT, C, SC> BabeApiServer for Babe<B, C, SC>
where
	B: BlockT,
	C: ProvideRuntimeApi<B>
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = BlockChainError>
		+ 'static,
	C::Api: BabeRuntimeApi<B>,
	SC: SelectChain<B> + Clone + 'static,
{
	async fn epoch_authorship(&self) -> Result<HashMap<AuthorityId, EpochAuthorship>, Error> {
		self.deny_unsafe.check_if_safe()?;

		let best_header = self.select_chain.best_chain().map_err(Error::SelectChain).await?;

		let epoch_start = self
			.client
			.runtime_api()
			.current_epoch_start(best_header.hash())
			.map_err(|_| Error::FetchEpoch)?;

		let epoch = self
			.babe_worker_handle
			.epoch_data_for_child_of(best_header.hash(), *best_header.number(), epoch_start)
			.await
			.map_err(|_| Error::FetchEpoch)?;

		let (epoch_start, epoch_end) = (epoch.start_slot(), epoch.end_slot());
		let mut claims: HashMap<AuthorityId, EpochAuthorship> = HashMap::new();

		let keys = {
			epoch
				.authorities
				.iter()
				.enumerate()
				.filter_map(|(i, a)| {
					if self.keystore.has_keys(&[(a.0.to_raw_vec(), AuthorityId::ID)]) {
						Some((a.0.clone(), i))
					} else {
						None
					}
				})
				.collect::<Vec<_>>()
		};

		for slot in *epoch_start..*epoch_end {
			if let Some((claim, key)) =
				authorship::claim_slot_using_keys(slot.into(), &epoch, &self.keystore, &keys)
			{
				match claim {
					PreDigest::Primary { .. } => {
						claims.entry(key).or_default().primary.push(slot);
					},
					PreDigest::SecondaryPlain { .. } => {
						claims.entry(key).or_default().secondary.push(slot);
					},
					PreDigest::SecondaryVRF { .. } => {
						claims.entry(key).or_default().secondary_vrf.push(slot.into());
					},
				};
			}
		}

		Ok(claims)
	}
}

/// Holds information about the `slot`'s that can be claimed by a given key.
#[derive(Clone, Default, Debug, Deserialize, Serialize)]
pub struct EpochAuthorship {
	/// the array of primary slots that can be claimed
	primary: Vec<u64>,
	/// the array of secondary slots that can be claimed
	secondary: Vec<u64>,
	/// The array of secondary VRF slots that can be claimed.
	secondary_vrf: Vec<u64>,
}

/// Top-level error type for the RPC handler.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Failed to fetch the current best header.
	#[error("Failed to fetch the current best header: {0}")]
	SelectChain(ConsensusError),
	/// Failed to fetch epoch data.
	#[error("Failed to fetch epoch data")]
	FetchEpoch,
	/// Consensus error
	#[error(transparent)]
	Consensus(#[from] ConsensusError),
	/// Errors that can be formatted as a String
	#[error("{0}")]
	StringError(String),
	/// Call to an unsafe RPC was denied.
	#[error(transparent)]
	UnsafeRpcCalled(#[from] UnsafeRpcError),
}

impl From<Error> for ErrorObjectOwned {
	fn from(error: Error) -> Self {
		match error {
			Error::SelectChain(e) => ErrorObject::owned(BABE_ERROR + 1, e.to_string(), None::<()>),
			Error::FetchEpoch => ErrorObject::owned(BABE_ERROR + 2, error.to_string(), None::<()>),
			Error::Consensus(e) => ErrorObject::owned(BABE_ERROR + 3, e.to_string(), None::<()>),
			Error::StringError(e) => ErrorObject::owned(BABE_ERROR + 4, e, None::<()>),
			Error::UnsafeRpcCalled(e) => e.into(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_consensus_babe::ImportQueueParams;
	use sc_transaction_pool_api::{OffchainTransactionPoolFactory, RejectAllTxPool};
	use sp_consensus_babe::inherents::InherentDataProvider;
	use sp_core::{crypto::key_types::BABE, testing::TaskExecutor};
	use sp_keyring::Sr25519Keyring;
	use sp_keystore::{testing::MemoryKeystore, Keystore};
	use substrate_test_runtime_client::{
		runtime::Block, Backend, DefaultTestClientBuilderExt, TestClient, TestClientBuilder,
		TestClientBuilderExt,
	};

	fn create_keystore(authority: Sr25519Keyring) -> KeystorePtr {
		let keystore = MemoryKeystore::new();
		keystore
			.sr25519_generate_new(BABE, Some(&authority.to_seed()))
			.expect("Creates authority key");
		keystore.into()
	}

	fn test_babe_rpc_module(
		deny_unsafe: DenyUnsafe,
	) -> Babe<Block, TestClient, sc_consensus::LongestChain<Backend, Block>> {
		let builder = TestClientBuilder::new();
		let (client, longest_chain) = builder.build_with_longest_chain();
		let client = Arc::new(client);
		let task_executor = TaskExecutor::new();
		let keystore = create_keystore(Sr25519Keyring::Alice);

		let config = sc_consensus_babe::configuration(&*client).expect("config available");
		let slot_duration = config.slot_duration();

		let (block_import, link) =
			sc_consensus_babe::block_import(config.clone(), client.clone(), client.clone())
				.expect("can initialize block-import");

		let (_, babe_worker_handle) = sc_consensus_babe::import_queue(ImportQueueParams {
			link: link.clone(),
			block_import: block_import.clone(),
			justification_import: None,
			client: client.clone(),
			select_chain: longest_chain.clone(),
			create_inherent_data_providers: move |_, _| async move {
				Ok((InherentDataProvider::from_timestamp_and_slot_duration(
					0.into(),
					slot_duration,
				),))
			},
			spawner: &task_executor,
			registry: None,
			telemetry: None,
			offchain_tx_pool_factory: OffchainTransactionPoolFactory::new(
				RejectAllTxPool::default(),
			),
		})
		.unwrap();

		Babe::new(client.clone(), babe_worker_handle, keystore, longest_chain, deny_unsafe)
	}

	#[tokio::test]
	async fn epoch_authorship_works() {
		let babe_rpc = test_babe_rpc_module(DenyUnsafe::No);
		let api = babe_rpc.into_rpc();

		let request = r#"{"jsonrpc":"2.0","method":"babe_epochAuthorship","params": [],"id":1}"#;
		let (response, _) = api.raw_json_request(request, 1).await.unwrap();
		let expected = r#"{"jsonrpc":"2.0","result":{"5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY":{"primary":[0],"secondary":[1,2,4],"secondary_vrf":[]}},"id":1}"#;

		assert_eq!(&response.result, expected);
	}

	#[tokio::test]
	async fn epoch_authorship_is_unsafe() {
		let babe_rpc = test_babe_rpc_module(DenyUnsafe::Yes);
		let api = babe_rpc.into_rpc();

		let request = r#"{"jsonrpc":"2.0","method":"babe_epochAuthorship","params":[],"id":1}"#;
		let (response, _) = api.raw_json_request(request, 1).await.unwrap();
		let expected = r#"{"jsonrpc":"2.0","error":{"code":-32601,"message":"RPC call is unsafe to be called externally"},"id":1}"#;

		assert_eq!(&response.result, expected);
	}
}
