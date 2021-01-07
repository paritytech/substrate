// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Light client blockchain backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::sync::Arc;

use sp_runtime::{Justification, generic::BlockId};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero};

use sp_blockchain::{
	HeaderMetadata, CachedHeaderMetadata, Error as ClientError, Result as ClientResult,
};
pub use sc_client_api::{
	backend::{
		AuxStore, NewBlockState, ProvideChtRoots,
	},
	blockchain::{
		Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
		HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo, ProvideCache,
		well_known_cache_keys,
	},
	light::{
		RemoteBlockchain, LocalOrRemote, Storage
	},
	cht,
};
use crate::fetcher::RemoteHeaderRequest;

/// Light client blockchain.
pub struct Blockchain<S> {
	storage: S,
}

impl<S> Blockchain<S> {
	/// Create new light blockchain backed with given storage.
	pub fn new(storage: S) -> Self {
		Self {
			storage,
		}
	}

	/// Get storage reference.
	pub fn storage(&self) -> &S {
		&self.storage
	}
}

impl<S, Block> BlockchainHeaderBackend<Block> for Blockchain<S> where Block: BlockT, S: Storage<Block> {
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		match RemoteBlockchain::header(self, id)? {
			LocalOrRemote::Local(header) => Ok(Some(header)),
			LocalOrRemote::Remote(_) => Err(ClientError::NotAvailableOnLightClient),
			LocalOrRemote::Unknown => Ok(None),
		}
	}

	fn info(&self) -> BlockchainInfo<Block> {
		self.storage.info()
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<BlockStatus> {
		self.storage.status(id)
	}

	fn number(&self, hash: Block::Hash) -> ClientResult<Option<NumberFor<Block>>> {
		self.storage.number(hash)
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Option<Block::Hash>> {
		self.storage.hash(number)
	}
}

impl<S, Block> HeaderMetadata<Block> for Blockchain<S> where Block: BlockT, S: Storage<Block> {
	type Error = ClientError;

	fn header_metadata(&self, hash: Block::Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.storage.header_metadata(hash)
	}

	fn insert_header_metadata(&self, hash: Block::Hash, metadata: CachedHeaderMetadata<Block>) {
		self.storage.insert_header_metadata(hash, metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.storage.remove_header_metadata(hash)
	}
}

impl<S, Block> BlockchainBackend<Block> for Blockchain<S> where Block: BlockT, S: Storage<Block> {
	fn body(&self, _id: BlockId<Block>) -> ClientResult<Option<Vec<Block::Extrinsic>>> {
		Err(ClientError::NotAvailableOnLightClient)
	}

	fn justification(&self, _id: BlockId<Block>) -> ClientResult<Option<Justification>> {
		Err(ClientError::NotAvailableOnLightClient)
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		self.storage.last_finalized()
	}

	fn cache(&self) -> Option<Arc<dyn BlockchainCache<Block>>> {
		self.storage.cache()
	}

	fn leaves(&self) -> ClientResult<Vec<Block::Hash>> {
		Err(ClientError::NotAvailableOnLightClient)
	}

	fn children(&self, _parent_hash: Block::Hash) -> ClientResult<Vec<Block::Hash>> {
		Err(ClientError::NotAvailableOnLightClient)
	}
}

impl<S: Storage<Block>, Block: BlockT> ProvideCache<Block> for Blockchain<S> {
	fn cache(&self) -> Option<Arc<dyn BlockchainCache<Block>>> {
		self.storage.cache()
	}
}

impl<S, Block: BlockT> RemoteBlockchain<Block> for Blockchain<S>
	where
		S: Storage<Block>,
{
	fn header(&self, id: BlockId<Block>) -> ClientResult<LocalOrRemote<
		Block::Header,
		RemoteHeaderRequest<Block::Header>,
	>> {
		// first, try to read header from local storage
		if let Some(local_header) = self.storage.header(id)? {
			return Ok(LocalOrRemote::Local(local_header));
		}

		// we need to know block number to check if it's a part of CHT
		let number = match id {
			BlockId::Hash(hash) => match self.storage.number(hash)? {
				Some(number) => number,
				None => return Ok(LocalOrRemote::Unknown),
			},
			BlockId::Number(number) => number,
		};

		// if the header is genesis (never pruned), non-canonical, or from future => return
		if number.is_zero() || self.storage.status(BlockId::Number(number))? == BlockStatus::Unknown {
			return Ok(LocalOrRemote::Unknown);
		}

		Ok(LocalOrRemote::Remote(RemoteHeaderRequest {
			cht_root: match self.storage.header_cht_root(cht::size(), number)? {
				Some(cht_root) => cht_root,
				None => return Ok(LocalOrRemote::Unknown),
			},
			block: number,
			retry_count: None,
		}))
	}
}

impl<S: Storage<Block>, Block: BlockT> ProvideChtRoots<Block> for Blockchain<S> {
	fn header_cht_root(
		&self,
		cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.storage().header_cht_root(cht_size, block)
	}

	fn changes_trie_cht_root(
		&self,
		cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.storage().changes_trie_cht_root(cht_size, block)
	}
}
