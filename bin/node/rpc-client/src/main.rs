// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![warn(missing_docs)]

//! Example substrate RPC client code.
//!
//! This module shows how you can write a Rust RPC client that connects to a running
//! substrate node and use statically typed RPC wrappers.

use futures::{Future, TryFutureExt};
use jsonrpc_core_client::{transports::http, RpcError};
use node_primitives::Hash;
use sc_rpc::author::{hash::ExtrinsicOrHash, AuthorClient};

fn main() -> Result<(), RpcError> {
	sp_tracing::try_init_simple();

	futures::executor::block_on(async {
		let uri = "http://localhost:9933";

		http::connect(uri)
			.and_then(|client: AuthorClient<Hash, Hash>| remove_all_extrinsics(client))
			.await
	})
}

/// Remove all pending extrinsics from the node.
///
/// The example code takes `AuthorClient` and first:
/// 1. Calls the `pending_extrinsics` method to get all extrinsics in the pool.
/// 2. Then calls `remove_extrinsic` passing the obtained raw extrinsics.
///
/// As the result of running the code the entire content of the transaction pool is going
/// to be removed and the extrinsics are going to be temporarily banned.
fn remove_all_extrinsics(
	client: AuthorClient<Hash, Hash>,
) -> impl Future<Output = Result<(), RpcError>> {
	client
		.pending_extrinsics()
		.and_then(move |pending| {
			client.remove_extrinsic(
				pending.into_iter().map(|tx| ExtrinsicOrHash::Extrinsic(tx.into())).collect(),
			)
		})
		.map_ok(|removed| {
			println!("Removed extrinsics: {:?}", removed);
		})
}
