// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
use assert_matches::assert_matches;
use jsonrpsee::{core::Error as JsonRpseeError, types::error::CallError};
use sc_block_builder::BlockBuilderProvider;
use sp_blockchain::HeaderBackend;
use sp_consensus::BlockOrigin;
use substrate_test_runtime_client::{prelude::*, runtime::Block};

#[tokio::test]
async fn block_stats_work() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = <Dev<Block, _>>::new(client.clone(), DenyUnsafe::No).into_rpc();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
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
			witness_len: 597,
			witness_compact_len: 500,
			block_len: 99,
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

	assert_matches!(
		api.call::<_, Option<BlockStats>>("dev_getBlockStats", [client.info().best_hash])
			.await,
		Err(JsonRpseeError::Call(CallError::Custom(err))) if err.message().contains("RPC call is unsafe to be called externally")
	);
}
