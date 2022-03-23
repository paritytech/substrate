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
use futures::executor;
use sc_block_builder::BlockBuilderProvider;
use sp_blockchain::HeaderBackend;
use sp_consensus::BlockOrigin;
use substrate_test_runtime_client::{prelude::*, runtime::Block};

#[test]
fn block_stats_work() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = <Dev<Block, _>>::new(client.clone(), DenyUnsafe::No);

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	executor::block_on(client.import(BlockOrigin::Own, block)).unwrap();

	// Can't gather stats for a block without a parent.
	assert_eq!(api.block_stats(client.genesis_hash()).unwrap(), None);

	assert_eq!(
		api.block_stats(client.info().best_hash).unwrap(),
		Some(BlockStats {
			witness_len: 597,
			witness_compact_len: 500,
			block_len: 99,
			num_extrinsics: 0,
		}),
	);
}

#[test]
fn deny_unsafe_works() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = <Dev<Block, _>>::new(client.clone(), DenyUnsafe::Yes);

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	executor::block_on(client.import(BlockOrigin::Own, block)).unwrap();

	assert_matches!(api.block_stats(client.info().best_hash), Err(Error::UnsafeRpcCalled(_)));
}
