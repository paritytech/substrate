// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Light client blockchin backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::sync::Weak;
use futures::{Future, IntoFuture};
use parking_lot::Mutex;

use primitives::AuthorityId;
use runtime_primitives::{Justification, generic::BlockId};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT,NumberFor, Zero};

use backend::NewBlockState;
use blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use cht;
use error::{ErrorKind as ClientErrorKind, Result as ClientResult};
use light::fetcher::{Fetcher, RemoteHeaderRequest};

/// Light client blockchain storage.
pub trait Storage<Block: BlockT>: BlockchainHeaderBackend<Block> {
	/// Store new header. Should refuse to revert any finalized blocks.
	///
	/// Takes new authorities, the leaf state of the new block, and
	/// any auxiliary storage updates to place in the same operation.
	fn import_header(
		&self,
		header: Block::Header,
		authorities: Option<Vec<AuthorityId>>,
		state: NewBlockState,
		aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> ClientResult<()>;

	/// Mark historic header as finalized.
	fn finalize_header(&self, block: BlockId<Block>) -> ClientResult<()>;

	/// Get last finalized header.
	fn last_finalized(&self) -> ClientResult<Block::Hash>;

	/// Get CHT root for given block. Fails if the block is not pruned (not a part of any CHT).
	fn cht_root(&self, cht_size: u64, block: NumberFor<Block>) -> ClientResult<Block::Hash>;

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
		match self.storage.header(id)? {
			Some(header) => Ok(Some(header)),
			None => {
				let number = match id {
					BlockId::Hash(hash) => match self.storage.number(hash)? {
						Some(number) => number,
						None => return Ok(None),
					},
					BlockId::Number(number) => number,
				};

				// if the header is from future or genesis (we never prune genesis) => return
				if number.is_zero() || self.storage.status(BlockId::Number(number))? != BlockStatus::InChain {
					return Ok(None);
				}

				self.fetcher().upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
					.remote_header(RemoteHeaderRequest {
						cht_root: self.storage.cht_root(cht::SIZE, number)?,
						block: number,
						retry_count: None,
					})
					.into_future().wait()
					.map(Some)
			}
		}
	}

	fn info(&self) -> ClientResult<BlockchainInfo<Block>> {
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

impl<S, F, Block> BlockchainBackend<Block> for Blockchain<S, F> where Block: BlockT, S: Storage<Block>, F: Fetcher<Block> {
	fn body(&self, _id: BlockId<Block>) -> ClientResult<Option<Vec<Block::Extrinsic>>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, _id: BlockId<Block>) -> ClientResult<Option<Justification>> {
		Ok(None)
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		self.storage.last_finalized()
	}

	fn cache(&self) -> Option<&BlockchainCache<Block>> {
		self.storage.cache()
	}

	fn leaves(&self) -> ClientResult<Vec<Block::Hash>> {
		unimplemented!()
	}
}
