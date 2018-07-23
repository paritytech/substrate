// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Light client blockchin backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::sync::Weak;
use parking_lot::Mutex;

use primitives::AuthorityId;
use runtime_primitives::{bft::Justification, generic::BlockId};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};

use blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use error::Result as ClientResult;
use light::fetcher::Fetcher;

/// Light client blockchain storage.
pub trait Storage<Block: BlockT>: BlockchainHeaderBackend<Block> {
	/// Store new header.
	fn import_header(
		&self,
		is_new_best: bool,
		header: Block::Header,
		authorities: Option<Vec<AuthorityId>>
	) -> ClientResult<()>;

	/// Get storage cache.
	fn cache(&self) -> Option<&BlockchainCache<Block>>;
}

/// Light client blockchain.
pub struct Blockchain<S, F> {
	fetcher: Mutex<Weak<F>>,
	storage: S,
}

impl<S, F> Blockchain<S, F> {
	/// Create new light blockchain backed with given storage.
	pub fn new(storage: S) -> Self {
		Self {
			fetcher: Mutex::new(Default::default()),
			storage,
		}
	}

	/// Sets fetcher reference.
	pub fn set_fetcher(&self, fetcher: Weak<F>) {
		*self.fetcher.lock() = fetcher;
	}

	/// Get fetcher weak reference.
	pub fn fetcher(&self) -> Weak<F> {
		self.fetcher.lock().clone()
	}

	/// Get storage reference.
	pub fn storage(&self) -> &S {
		&self.storage
	}
}

impl<S, F, Block> BlockchainHeaderBackend<Block> for Blockchain<S, F> where Block: BlockT, S: Storage<Block>, F: Fetcher<Block> {
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		self.storage.header(id)
	}

	fn info(&self) -> ClientResult<BlockchainInfo<Block>> {
		self.storage.info()
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<BlockStatus> {
		self.storage.status(id)
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Option<Block::Hash>> {
		self.storage.hash(number)
	}
}

impl<S, F, Block> BlockchainBackend<Block> for Blockchain<S, F> where Block: BlockT, S: Storage<Block>, F: Fetcher<Block> {
	fn body(&self, _id: BlockId<Block>) -> ClientResult<Option<Vec<Block::Extrinsic>>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, _id: BlockId<Block>) -> ClientResult<Option<Justification<Block::Hash>>> {
		Ok(None)
	}

	fn cache(&self) -> Option<&BlockchainCache<Block>> {
		self.storage.cache()
	}
}
