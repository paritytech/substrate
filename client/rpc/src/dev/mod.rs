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

//! Implementation of the [`DevApiServer`] trait providing debug utilities for Substrate based
//! blockchains.

#[cfg(test)]
mod tests;

use jsonrpsee::core::RpcResult;
use sc_client_api::{BlockBackend, HeaderBackend};
use sc_rpc_api::{dev::error::Error, DenyUnsafe};
use sp_api::{ApiExt, Core, ProvideRuntimeApi};
use sp_core::Encode;
use sp_runtime::{
	generic::DigestItem,
	traits::{Block as BlockT, Header},
};
use std::{
	marker::{PhantomData, Send, Sync},
	sync::Arc,
};

pub use sc_rpc_api::dev::{BlockStats, DevApiServer};

type HasherOf<Block> = <<Block as BlockT>::Header as Header>::Hashing;

/// The Dev API. All methods are unsafe.
pub struct Dev<Block: BlockT, Client> {
	client: Arc<Client>,
	deny_unsafe: DenyUnsafe,
	_phantom: PhantomData<Block>,
}

impl<Block: BlockT, Client> Dev<Block, Client> {
	/// Create a new Dev API.
	pub fn new(client: Arc<Client>, deny_unsafe: DenyUnsafe) -> Self {
		Self { client, deny_unsafe, _phantom: PhantomData::default() }
	}
}

impl<Block, Client> DevApiServer<Block::Hash> for Dev<Block, Client>
where
	Block: BlockT + 'static,
	Client: BlockBackend<Block>
		+ HeaderBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: Core<Block>,
{
	fn block_stats(&self, hash: Block::Hash) -> RpcResult<Option<BlockStats>> {
		self.deny_unsafe.check_if_safe()?;

		let block = {
			let block = self.client.block(hash).map_err(|e| Error::BlockQueryError(Box::new(e)))?;
			if let Some(block) = block {
				let (mut header, body) = block.block.deconstruct();
				// Remove the `Seal` to ensure we have the number of digests as expected by the
				// runtime.
				header.digest_mut().logs.retain(|item| !matches!(item, DigestItem::Seal(_, _)));
				Block::new(header, body)
			} else {
				return Ok(None)
			}
		};
		let parent_header = {
			let parent_hash = *block.header().parent_hash();
			let parent_header = self
				.client
				.header(parent_hash)
				.map_err(|e| Error::BlockQueryError(Box::new(e)))?;
			if let Some(header) = parent_header {
				header
			} else {
				return Ok(None)
			}
		};
		let block_len = block.encoded_size() as u64;
		let num_extrinsics = block.extrinsics().len() as u64;
		let pre_root = *parent_header.state_root();
		let mut runtime_api = self.client.runtime_api();
		runtime_api.record_proof();
		runtime_api
			.execute_block(parent_header.hash(), block)
			.map_err(|_| Error::BlockExecutionFailed)?;
		let witness = runtime_api
			.extract_proof()
			.expect("We enabled proof recording. A proof must be available; qed");
		let witness_len = witness.encoded_size() as u64;
		let witness_compact_len = witness
			.into_compact_proof::<HasherOf<Block>>(pre_root)
			.map_err(|_| Error::WitnessCompactionFailed)?
			.encoded_size() as u64;
		Ok(Some(BlockStats { witness_len, witness_compact_len, block_len, num_extrinsics }))
	}
}
