// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Basic example of end to end runtime tests.

use test_runner::{Node, ChainInfo, SignatureVerificationOverride};
use grandpa::GrandpaBlockImport;
use sc_service::{TFullBackend, TFullClient, Configuration, TaskManager, new_full_parts};
use std::sync::Arc;
use sp_inherents::InherentDataProviders;
use sc_consensus_babe::BabeBlockImport;
use sp_keystore::SyncCryptoStorePtr;
use sp_keyring::sr25519::Keyring::Alice;
use sp_consensus_babe::AuthorityId;
use sc_consensus_manual_seal::{ConsensusDataProvider, consensus::babe::BabeConsensusDataProvider};
use sp_runtime::{traits::IdentifyAccount, MultiSigner, generic::Era};

type BlockImport<B, BE, C, SC> = BabeBlockImport<B, C, GrandpaBlockImport<BE, B, C, SC>>;

sc_executor::native_executor_instance!(
	pub Executor,
	node_runtime::api::dispatch,
	node_runtime::native_version,
	(
		frame_benchmarking::benchmarking::HostFunctions,
		SignatureVerificationOverride,
	)
);

/// ChainInfo implementation.
struct NodeTemplateChainInfo;

impl ChainInfo for NodeTemplateChainInfo {
	type Block = node_primitives::Block;
	type Executor = Executor;
	type Runtime = node_runtime::Runtime;
	type RuntimeApi = node_runtime::RuntimeApi;
	type SelectChain = sc_consensus::LongestChain<TFullBackend<Self::Block>, Self::Block>;
	type BlockImport = BlockImport<
		Self::Block,
		TFullBackend<Self::Block>,
		TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
		Self::SelectChain,
	>;
	type SignedExtras = node_runtime::SignedExtra;

	fn signed_extras(from: <Self::Runtime as frame_system::Config>::AccountId) -> Self::SignedExtras {
		(
			frame_system::CheckSpecVersion::<Self::Runtime>::new(),
			frame_system::CheckTxVersion::<Self::Runtime>::new(),
			frame_system::CheckGenesis::<Self::Runtime>::new(),
			frame_system::CheckMortality::<Self::Runtime>::from(Era::Immortal),
			frame_system::CheckNonce::<Self::Runtime>::from(frame_system::Pallet::<Self::Runtime>::account_nonce(from)),
			frame_system::CheckWeight::<Self::Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Self::Runtime>::from(0),
		)
	}

	fn create_client_parts(
		config: &Configuration,
	) -> Result<
		(
			Arc<TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>>,
			Arc<TFullBackend<Self::Block>>,
			SyncCryptoStorePtr,
			TaskManager,
			InherentDataProviders,
			Option<
				Box<
					dyn ConsensusDataProvider<
						Self::Block,
						Transaction = sp_api::TransactionFor<
							TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
							Self::Block,
						>,
					>,
				>,
			>,
			Self::SelectChain,
			Self::BlockImport,
		),
		sc_service::Error,
	> {
		let (client, backend, keystore, task_manager) =
			new_full_parts::<Self::Block, Self::RuntimeApi, Self::Executor>(config, None)?;
		let client = Arc::new(client);

		let inherent_providers = InherentDataProviders::new();
		let select_chain = sc_consensus::LongestChain::new(backend.clone());

		let (grandpa_block_import, ..) =
			grandpa::block_import(
				client.clone(),
				&(client.clone() as Arc<_>),
				select_chain.clone(),
				None
			)?;

		let (block_import, babe_link) = sc_consensus_babe::block_import(
			sc_consensus_babe::Config::get_or_compute(&*client)?,
			grandpa_block_import,
			client.clone(),
		)?;

		let consensus_data_provider = BabeConsensusDataProvider::new(
			client.clone(),
			keystore.sync_keystore(),
			&inherent_providers,
			babe_link.epoch_changes().clone(),
			vec![(AuthorityId::from(Alice.public()), 1000)],
		)
			.expect("failed to create ConsensusDataProvider");

		Ok((
			client,
			backend,
			keystore.sync_keystore(),
			task_manager,
			inherent_providers,
			Some(Box::new(consensus_data_provider)),
			select_chain,
			block_import,
		))
	}

	fn dispatch_with_root(call: <Self::Runtime as frame_system::Config>::Call, node: &mut Node<Self>) {
		let alice = MultiSigner::from(Alice.public()).into_account();
		let call = pallet_sudo::Call::sudo(Box::new(call));
		node.submit_extrinsic(call, alice);
		node.seal_blocks(1);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use test_runner::NodeConfig;
	use log::LevelFilter;
	use sc_client_api::execution_extensions::ExecutionStrategies;
	use node_cli::chain_spec::development_config;

	#[test]
	fn test_runner() {
		let config = NodeConfig {
			execution_strategies: ExecutionStrategies {
				syncing: sc_client_api::ExecutionStrategy::AlwaysWasm,
				importing: sc_client_api::ExecutionStrategy::AlwaysWasm,
				block_construction: sc_client_api::ExecutionStrategy::AlwaysWasm,
				offchain_worker: sc_client_api::ExecutionStrategy::AlwaysWasm,
				other: sc_client_api::ExecutionStrategy::AlwaysWasm,
			},
			chain_spec: Box::new(development_config()),
			log_targets: vec![
				("yamux", LevelFilter::Off),
				("multistream_select", LevelFilter::Off),
				("libp2p", LevelFilter::Off),
				("jsonrpc_client_transports", LevelFilter::Off),
				("sc_network", LevelFilter::Off),
				("tokio_reactor", LevelFilter::Off),
				("parity-db", LevelFilter::Off),
				("sub-libp2p", LevelFilter::Off),
				("sync", LevelFilter::Off),
				("peerset", LevelFilter::Off),
				("ws", LevelFilter::Off),
				("sc_network", LevelFilter::Off),
				("sc_service", LevelFilter::Off),
				("sc_basic_authorship", LevelFilter::Off),
				("telemetry-logger", LevelFilter::Off),
				("sc_peerset", LevelFilter::Off),
				("rpc", LevelFilter::Off),
				("runtime", LevelFilter::Trace),
				("babe", LevelFilter::Debug)
			],
		};
		let mut node = Node::<NodeTemplateChainInfo>::new(config).unwrap();
		// seals blocks
		node.seal_blocks(1);
		// submit extrinsics
		let alice = MultiSigner::from(Alice.public()).into_account();
		node.submit_extrinsic(frame_system::Call::remark((b"hello world").to_vec()), alice);

		// look ma, I can read state.
		let _events = node.with_state(|| frame_system::Pallet::<node_runtime::Runtime>::events());
		// get access to the underlying client.
		let _client = node.client();
	}
}
