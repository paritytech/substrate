// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Light client blockchain backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::{sync::{Weak, Arc}, collections::HashMap};
use futures::{Future, IntoFuture};
use parking_lot::Mutex;

use runtime_primitives::{Justification, generic::BlockId};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero};
use consensus::well_known_cache_keys;

use crate::backend::{AuxStore, NewBlockState};
use crate::blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo, ProvideCache};
use crate::cht;
use crate::error::{Error as ClientError, Result as ClientResult};
use crate::light::fetcher::{Fetcher, RemoteHeaderRequest};

/// Light client blockchain storage.
pub trait Storage<Block: BlockT>: AuxStore + BlockchainHeaderBackend<Block> {
	/// Store new header. Should refuse to revert any finalized blocks.
	///
	/// Takes new authorities, the leaf state of the new block, and
	/// any auxiliary storage updates to place in the same operation.
	fn import_header(
		&self,
		header: Block::Header,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		state: NewBlockState,
		aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> ClientResult<()>;

	/// Set an existing block as new best block.
	fn set_head(&self, block: BlockId<Block>) -> ClientResult<()>;

	/// Mark historic header as finalized.
	fn finalize_header(&self, block: BlockId<Block>) -> ClientResult<()>;

	/// Get last finalized header.
	fn last_finalized(&self) -> ClientResult<Block::Hash>;

	/// Get headers CHT root for given block. Fails if the block is not pruned (not a part of any CHT).
	fn header_cht_root(&self, cht_size: u64, block: NumberFor<Block>) -> ClientResult<Block::Hash>;

	/// Get changes trie CHT root for given block. Fails if the block is not pruned (not a part of any CHT).
	fn changes_trie_cht_root(&self, cht_size: u64, block: NumberFor<Block>) -> ClientResult<Block::Hash>;

	/// Get storage cache.
	fn cache(&self) -> Option<Arc<BlockchainCache<Block>>>;
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
				if number.is_zero() || self.storage.status(BlockId::Number(number))? == BlockStatus::Unknown {
					return Ok(None);
				}

				self.fetcher().upgrade().ok_or(ClientError::NotAvailableOnLightClient)?
					.remote_header(RemoteHeaderRequest {
						cht_root: self.storage.header_cht_root(cht::SIZE, number)?,
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
		// TODO: #1445 fetch from remote node
		Ok(None)
	}

	fn justification(&self, _id: BlockId<Block>) -> ClientResult<Option<Justification>> {
		Ok(None)
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		self.storage.last_finalized()
	}

	fn cache(&self) -> Option<Arc<BlockchainCache<Block>>> {
		self.storage.cache()
	}

	fn leaves(&self) -> ClientResult<Vec<Block::Hash>> {
		unimplemented!()
	}

	fn children(&self, _parent_hash: Block::Hash) -> ClientResult<Vec<Block::Hash>> {
		unimplemented!()
	}
}

impl<S: Storage<Block>, F, Block: BlockT> ProvideCache<Block> for Blockchain<S, F> {
	fn cache(&self) -> Option<Arc<BlockchainCache<Block>>> {
		self.storage.cache()
	}
}

#[cfg(test)]
pub mod tests {
	use std::collections::HashMap;
	use test_client::runtime::{Hash, Block, Header};
	use crate::blockchain::Info;
	use crate::light::fetcher::tests::OkCallFetcher;
	use super::*;

	pub type DummyBlockchain = Blockchain<DummyStorage, OkCallFetcher>;

	pub struct DummyStorage {
		pub changes_tries_cht_roots: HashMap<u64, Hash>,
		pub aux_store: Mutex<HashMap<Vec<u8>, Vec<u8>>>,
	}

	impl DummyStorage {
		pub fn new() -> Self {
			DummyStorage {
				changes_tries_cht_roots: HashMap::new(),
				aux_store: Mutex::new(HashMap::new()),
			}
		}
	}

	impl BlockchainHeaderBackend<Block> for DummyStorage {
		fn header(&self, _id: BlockId<Block>) -> ClientResult<Option<Header>> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn info(&self) -> ClientResult<Info<Block>> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn status(&self, _id: BlockId<Block>) -> ClientResult<BlockStatus> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn number(&self, hash: Hash) -> ClientResult<Option<NumberFor<Block>>> {
			if hash == Default::default() {
				Ok(Some(Default::default()))
			} else {
				Err(ClientError::Backend("Test error".into()))
			}
		}

		fn hash(&self, number: u64) -> ClientResult<Option<Hash>> {
			if number == 0 {
				Ok(Some(Default::default()))
			} else {
				Err(ClientError::Backend("Test error".into()))
			}
		}
	}

	impl AuxStore for DummyStorage {
		fn insert_aux<
			'a,
			'b: 'a,
			'c: 'a,
			I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
			D: IntoIterator<Item=&'a &'b [u8]>,
		>(&self, insert: I, _delete: D) -> ClientResult<()> {
			for (k, v) in insert.into_iter() {
				self.aux_store.lock().insert(k.to_vec(), v.to_vec());
			}
			Ok(())
		}

		fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
			Ok(self.aux_store.lock().get(key).cloned())
		}
	}

	impl Storage<Block> for DummyStorage {
		fn import_header(
			&self,
			_header: Header,
			_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
			_state: NewBlockState,
			_aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		) -> ClientResult<()> {
			Ok(())
		}

		fn set_head(&self, _block: BlockId<Block>) -> ClientResult<()> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn finalize_header(&self, _block: BlockId<Block>) -> ClientResult<()> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn last_finalized(&self) -> ClientResult<Hash> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn header_cht_root(&self, _cht_size: u64, _block: u64) -> ClientResult<Hash> {
			Err(ClientError::Backend("Test error".into()))
		}

		fn changes_trie_cht_root(&self, cht_size: u64, block: u64) -> ClientResult<Hash> {
			cht::block_to_cht_number(cht_size, block)
				.and_then(|cht_num| self.changes_tries_cht_roots.get(&cht_num))
				.cloned()
				.ok_or_else(|| ClientError::Backend(
					format!("Test error: CHT for block #{} not found", block)
				).into())
		}

		fn cache(&self) -> Option<Arc<BlockchainCache<Block>>> {
			None
		}
	}
}
