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

use crate::{service::network::NetworkServiceProvider, ChainSync, ForkTarget};

use libp2p::PeerId;
use sc_network_common::{service::NetworkSyncForkRequest, sync::ChainSync as ChainSyncT};
use sp_consensus::block_validation::DefaultBlockAnnounceValidator;
use sp_core::H256;
use std::{sync::Arc, task::Poll};
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

// verify that the fork target map is empty, then submit a new sync fork request,
// poll `ChainSync` and verify that a new sync fork request has been registered
#[async_std::test]
async fn delegate_to_chainsync() {
	let (_chain_sync_network_provider, chain_sync_network_handle) = NetworkServiceProvider::new();
	let (mut chain_sync, chain_sync_service) = ChainSync::new(
		sc_network_common::sync::SyncMode::Full,
		Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0),
		Box::new(DefaultBlockAnnounceValidator),
		1u32,
		None,
		chain_sync_network_handle,
	)
	.unwrap();

	let hash = H256::random();
	let in_number = 1337u64;
	let peers = (0..3).map(|_| PeerId::random()).collect::<Vec<_>>();

	assert!(chain_sync.fork_targets.is_empty());
	chain_sync_service.set_sync_fork_request(peers, hash, in_number);

	futures::future::poll_fn(|cx| {
		let _ = chain_sync.poll(cx);
		Poll::Ready(())
	})
	.await;

	if let Some(ForkTarget { number, .. }) = chain_sync.fork_targets.get(&hash) {
		assert_eq!(number, &in_number);
	} else {
		panic!("expected to contain `ForkTarget`");
	}
}
