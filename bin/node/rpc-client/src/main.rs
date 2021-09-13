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

use futures::TryFutureExt;
use jsonrpsee::{types::Error, ws_client::WsClientBuilder};
use node_primitives::Hash;
use sc_rpc::author::{hash::ExtrinsicOrHash, AuthorApiClient};

#[tokio::main]
async fn main() -> Result<(), Error> {
	sp_tracing::try_init_simple();

	// TODO(niklasad1):  https://github.com/paritytech/jsonrpsee/issues/448
	// changed this to the WS client because the jsonrpsee proc macros
	// requires the trait bound `SubscriptionClient` which is not implemented for the HTTP client.
	WsClientBuilder::default()
		.build("ws://localhost:9944")
		.and_then(|client| remove_all_extrinsics(client))
		.await
}

/// Remove all pending extrinsics from the node.
///
/// The example code takes `AuthorClient` and first:
/// 1. Calls the `pending_extrinsics` method to get all extrinsics in the pool.
/// 2. Then calls `remove_extrinsic` passing the obtained raw extrinsics.
///
/// As the result of running the code the entire content of the transaction pool is going
/// to be removed and the extrinsics are going to be temporarily banned.
async fn remove_all_extrinsics<C>(client: C) -> Result<(), Error>
where
	C: AuthorApiClient<Hash, Hash> + Sync,
{
	let pending_exts = client.pending_extrinsics().await?;
	let removed = client
		.remove_extrinsic(
			pending_exts
				.into_iter()
				.map(|tx| ExtrinsicOrHash::Extrinsic(tx.into()))
				.collect(),
		)
		.await?;
	println!("Removed extrinsics: {:?}", removed);
	Ok(())
}
