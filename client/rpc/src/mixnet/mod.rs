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

//! Substrate mixnet API.

use jsonrpsee::core::{async_trait, RpcResult};
use sc_mixnet::Api;
use sc_rpc_api::mixnet::error::Error;
pub use sc_rpc_api::mixnet::MixnetApiServer;
use sp_core::Bytes;

/// Mixnet API.
pub struct Mixnet(futures::lock::Mutex<Api>);

impl Mixnet {
	/// Create a new mixnet API instance.
	pub fn new(api: Api) -> Self {
		Self(futures::lock::Mutex::new(api))
	}
}

#[async_trait]
impl MixnetApiServer for Mixnet {
	async fn submit_extrinsic(&self, extrinsic: Bytes) -> RpcResult<()> {
		// We only hold the lock while pushing the request into the requests channel
		let fut = {
			let mut api = self.0.lock().await;
			api.submit_extrinsic(extrinsic).await
		};
		Ok(fut.await.map_err(Error)?)
	}
}
