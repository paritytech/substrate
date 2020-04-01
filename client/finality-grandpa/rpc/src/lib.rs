// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! RPC API for GRANDPA.

use futures::{FutureExt as _, TryFutureExt as _};
use jsonrpc_derive::rpc;
use jsonrpc_core::{Error as RpcError, futures::future as rpc_future};

type FutureResult<T> = Box<dyn rpc_future::Future<Item = T, Error = RpcError> + Send>;

#[rpc]
pub trait GrandpaApi {
	#[rpc(name = "grandpa_roundState")]
	fn grandpa_roundState(&self) -> FutureResult<String>;
}

pub struct GrandpaRpcHandler;

impl GrandpaApi for GrandpaRpcHandler {
	fn grandpa_roundState(&self) -> FutureResult<String> {
		let future = async move {
			Ok(String::from("Hello world"))
		}.boxed();
		Box::new(future.compat())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_test_runtime_client::{
		DefaultTestClientBuilderExt,
		TestClientBuilder,
		TestClientBuilderExt,
	};
	use std::sync::Arc;
	use jsonrpc_core::IoHandler;

	#[test]
	fn round_state() {
		let builder = TestClientBuilder::new();
		let client = builder.build();
		let client = Arc::new(client);

		let handler = GrandpaRpcHandler {};
		let mut io = IoHandler::new();
		io.extend_with(GrandpaApi::to_delegate(handler));

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","result":"Hello world","id":1}"#;

		assert_eq!(Some(response.into()), io.handle_request_sync(request));
	}
}
