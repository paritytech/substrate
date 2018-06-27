// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate block-author/full-node API.

use std::sync::Arc;

use client::{self, Client};
use extrinsic_pool::api::{Error, ExtrinsicPool};
use codec::Slicable;

use primitives::Bytes;
use runtime_primitives::{generic, traits::Block as BlockT};
use state_machine;

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate authoring RPC API
	pub trait AuthorApi<Hash, Extrinsic> {
		/// Submit extrinsic for inclusion in block.
		#[rpc(name = "author_submitRichExtrinsic")]
		fn submit_rich_extrinsic(&self, Extrinsic) -> Result<Hash>;
		/// Submit hex-encoded extrinsic for inclusion in block.
		#[rpc(name = "author_submitExtrinsic")]
		fn submit_extrinsic(&self, Bytes) -> Result<Hash>;
	}
}

/// Authoring API
pub struct Author<B, E, Block: BlockT, P> {
	/// Substrate client
	client: Arc<Client<B, E, Block>>,
	/// Extrinsic pool
	pool: Arc<P>,
}

impl<B, E, Block: BlockT, P> Author<B, E, Block, P> {
	/// Create new instance of Authoring API.
	pub fn new(client: Arc<Client<B, E, Block>>, pool: Arc<P>) -> Self {
		Author { client, pool }
	}
}

impl<B, E, Block, P, Ex, Hash> AuthorApi<Hash, Ex> for Author<B, E, Block, P> where
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: client::CallExecutor<Block> + Send + Sync + 'static,
	Block: BlockT + 'static,
	client::error::Error: From<<<B as client::backend::Backend<Block>>::State as state_machine::backend::Backend>::Error>,
	P: ExtrinsicPool<Ex, generic::BlockId<Block>, Hash>,
	P::Error: 'static,
	Ex: Slicable,
{
	fn submit_extrinsic(&self, xt: Bytes) -> Result<Hash> {
		self.submit_rich_extrinsic(Ex::decode(&mut &xt[..]).ok_or(error::Error::from(error::ErrorKind::BadFormat))?)
	}

	fn submit_rich_extrinsic(&self, xt: Ex) -> Result<Hash> {
		let best_block_hash = self.client.info().unwrap().chain.best_hash;
		self.pool
			.submit(generic::BlockId::hash(best_block_hash), vec![xt])
			.map(|mut res| res.pop().expect("One extrinsic passed; one result back; qed"))
			.map_err(|e| e.into_pool_error()
				.map(Into::into)
				.unwrap_or_else(|e| error::ErrorKind::Verification(Box::new(e)).into())
			)
	}
}
