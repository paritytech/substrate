// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
//! Helper to run commands against current node RPC

use futures::Future;
use hyper::rt;
use node_primitives::Hash;
use sc_rpc::author::AuthorClient;
use jsonrpc_core_client::transports::http;
use sp_core::Bytes;

pub struct RpcClient { url: String }

impl RpcClient {
	pub fn new(url: String) -> Self { Self { url } }

	pub fn insert_key(
		&self,
		key_type: String,
		suri: String,
		public: Bytes,
	) {
		let url = self.url.clone();

		rt::run(
			http::connect(&url)
				.and_then(|client: AuthorClient<Hash, Hash>| {
					client.insert_key(key_type, suri, public).map(|_| ())
				})
				.map_err(|e| {
					eprintln!("Error inserting key: {:?}", e);
				})
		);
	}
}
