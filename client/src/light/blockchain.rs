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

use std::future::Future;
use std::sync::Arc;

use sp_runtime::{Justification, generic::BlockId};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero};

use sp_blockchain::{
	HeaderMetadata, CachedHeaderMetadata,
	Error as ClientError, Result as ClientResult,
};
pub use client_api::{
	backend::{
		AuxStore, NewBlockState
	},
	blockchain::{
		Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
		HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo, ProvideCache,
		well_known_cache_keys,
	},
	light::{
		RemoteBlockchain, LocalOrRemote, Storage
	}
};
use crate::cht;
use crate::light::fetcher::{Fetcher, RemoteHeaderRequest};

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
			cht_root: self.storage.header_cht_root(cht::size(), number)?,
			block: number,
			retry_count: None,
		}))
	}
}

/// Returns future that resolves header either locally, or remotely.
pub fn future_header<Block: BlockT, F: Fetcher<Block>>(
	blockchain: &dyn RemoteBlockchain<Block>,
	fetcher: &F,
	id: BlockId<Block>,
) -> impl Future<Output = Result<Option<Block::Header>, ClientError>> {
	use futures::future::{ready, Either, FutureExt};

	match blockchain.header(id) {
		Ok(LocalOrRemote::Remote(request)) => Either::Left(
			fetcher
				.remote_header(request)
				.then(|header| ready(header.map(Some)))
		),
		Ok(LocalOrRemote::Unknown) => Either::Right(ready(Ok(None))),
		Ok(LocalOrRemote::Local(local_header)) => Either::Right(ready(Ok(Some(local_header)))),
		Err(err) => Either::Right(ready(Err(err))),
	}
}

#[cfg(test)]
pub mod tests {
	use std::collections::HashMap;
	use parking_lot::Mutex;
	use test_client::runtime::{Hash, Block, Header};
	use client_api::blockchain::Info;
	use super::*;

	pub type DummyBlockchain = Blockchain<DummyStorage>;

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

		fn info(&self) -> Info<Block> {
			panic!("Test error")
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

	impl HeaderMetadata<Block> for DummyStorage {
		type Error = ClientError;

		fn header_metadata(&self, hash: Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
			self.header(BlockId::hash(hash))?.map(|header| CachedHeaderMetadata::from(&header))
				.ok_or(ClientError::UnknownBlock("header not found".to_owned()))
		}
		fn insert_header_metadata(&self, _hash: Hash, _metadata: CachedHeaderMetadata<Block>) {}
		fn remove_header_metadata(&self, _hash: Hash) {}
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

		fn cache(&self) -> Option<Arc<dyn BlockchainCache<Block>>> {
			None
		}
	}
}
