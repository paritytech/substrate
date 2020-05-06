// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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
