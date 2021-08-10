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
#![deny(unused_extern_crates, missing_docs)]

//! Basic example of end to end runtime tests.

use grandpa::GrandpaBlockImport;
use sc_consensus_babe::BabeBlockImport;
use sc_consensus_manual_seal::consensus::babe::SlotTimestampProvider;
use sc_service::{TFullBackend, TFullClient};
use sp_runtime::generic::Era;
use test_runner::{ChainInfo, SignatureVerificationOverride};

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
	type InherentDataProviders =
		(SlotTimestampProvider, sp_consensus_babe::inherents::InherentDataProvider);

	fn signed_extras(
		from: <Self::Runtime as frame_system::Config>::AccountId,
	) -> Self::SignedExtras {
		(
			frame_system::CheckSpecVersion::<Self::Runtime>::new(),
			frame_system::CheckTxVersion::<Self::Runtime>::new(),
			frame_system::CheckGenesis::<Self::Runtime>::new(),
			frame_system::CheckMortality::<Self::Runtime>::from(Era::Immortal),
			frame_system::CheckNonce::<Self::Runtime>::from(
				frame_system::Pallet::<Self::Runtime>::account_nonce(from),
			),
			frame_system::CheckWeight::<Self::Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Self::Runtime>::from(0),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use node_cli::chain_spec::development_config;
	use sp_keyring::sr25519::Keyring::Alice;
	use sp_runtime::{traits::IdentifyAccount, MultiSigner};
	use test_runner::{build_runtime, client_parts, task_executor, ConfigOrChainSpec, Node};

	#[test]
	fn test_runner() {
		let mut tokio_runtime = build_runtime().unwrap();
		let task_executor = task_executor(tokio_runtime.handle().clone());
		let (rpc, task_manager, client, pool, command_sink, backend) = client_parts::<
			NodeTemplateChainInfo,
		>(
			ConfigOrChainSpec::ChainSpec(Box::new(development_config()), task_executor),
		)
		.unwrap();
		let node = Node::<NodeTemplateChainInfo>::new(
			rpc,
			task_manager,
			client,
			pool,
			command_sink,
			backend,
		);

		tokio_runtime.block_on(async {
			// seals blocks
			node.seal_blocks(1).await;
			// submit extrinsics
			let alice = MultiSigner::from(Alice.public()).into_account();
			let _hash = node
				.submit_extrinsic(
					frame_system::Call::remark((b"hello world").to_vec()),
					Some(alice),
				)
				.await
				.unwrap();

			// look ma, I can read state.
			let _events =
				node.with_state(|| frame_system::Pallet::<node_runtime::Runtime>::events());
			// get access to the underlying client.
			let _client = node.client();
		})
	}
}
