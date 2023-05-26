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

use super::*;
use sc_block_builder::BlockBuilderProvider;
use sp_blockchain::HeaderBackend;
use sp_consensus::BlockOrigin;
use substrate_test_runtime_client::{prelude::*, runtime::Block};

#[tokio::test]
async fn block_stats_work() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = <Dev<Block, _>>::new(client.clone(), DenyUnsafe::No).into_rpc();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;

	let (expected_witness_len, expected_witness_compact_len, expected_block_len) = {
		let genesis_hash = client.chain_info().genesis_hash;
		let mut runtime_api = client.runtime_api();
		runtime_api.record_proof();
		runtime_api.execute_block(genesis_hash, block.clone()).unwrap();
		let witness = runtime_api.extract_proof().unwrap();
		let pre_root = *client.header(genesis_hash).unwrap().unwrap().state_root();

		(
			witness.clone().encoded_size() as u64,
			witness.into_compact_proof::<HasherOf<Block>>(pre_root).unwrap().encoded_size() as u64,
			block.encoded_size() as u64,
		)
	};

	client.import(BlockOrigin::Own, block).await.unwrap();

	// Can't gather stats for a block without a parent.
	assert_eq!(
		api.call::<_, Option<BlockStats>>("dev_getBlockStats", [client.genesis_hash()])
			.await
			.unwrap(),
		None
	);

	assert_eq!(
		api.call::<_, Option<BlockStats>>("dev_getBlockStats", [client.info().best_hash])
			.await
			.unwrap(),
		Some(BlockStats {
			witness_len: expected_witness_len,
			witness_compact_len: expected_witness_compact_len,
			block_len: expected_block_len,
			num_extrinsics: 0,
		}),
	);
}

#[tokio::test]
async fn deny_unsafe_works() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = <Dev<Block, _>>::new(client.clone(), DenyUnsafe::Yes).into_rpc();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block).await.unwrap();

	let best_hash = client.info().best_hash;
	let best_hash_param =
		serde_json::to_string(&best_hash).expect("To string must always succeed for block hashes");

	let request = format!(
		"{{\"jsonrpc\":\"2.0\",\"method\":\"dev_getBlockStats\",\"params\":[{}],\"id\":1}}",
		best_hash_param
	);
	let (resp, _) = api.raw_json_request(&request).await.expect("Raw calls should succeed");

	assert_eq!(
		resp.result,
		r#"{"jsonrpc":"2.0","error":{"code":-32601,"message":"RPC call is unsafe to be called externally"},"id":1}"#
	);
}
