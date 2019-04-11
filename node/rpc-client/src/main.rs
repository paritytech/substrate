// Copyright 2019 Parity Technologies (UK) Ltd.
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

use futures::Future;
use hyper::rt;
use node_primitives::Hash;
use substrate_rpc::author::AuthorClient;

mod http_client;

fn main() {
	env_logger::init();

	rt::run(rt::lazy(|| {
		let uri = "http://localhost:9933";

		http_client::http(uri)
			.and_then(|client: AuthorClient<Hash, Hash>| {
				client.pending_extrinsics()
					.then(move |pending| {
						println!("Pending: {:?}", pending);
						drop(client);
						Ok(())
					})
			})
	}))
}
