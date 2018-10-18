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

//! Light client backend. Only stores headers and justifications of blocks.
//! Everything else is requested from full nodes on demand.

use std::sync::{Arc, Weak};
use futures::{Future, IntoFuture};
use parking_lot::RwLock;

use primitives::AuthorityId;
use runtime_primitives::{generic::BlockId, Justification};
use state_machine::{Backend as StateBackend, InMemoryChangesTrieStorage, TrieBackend};
use runtime_primitives::traits::{Block as BlockT, NumberFor};

use backend::{Backend as ClientBackend, BlockImportOperation, RemoteBackend, NewBlockState};
use blockchain::HeaderBackend as BlockchainHeaderBackend;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::fetcher::{Fetcher, RemoteReadRequest};
use hash_db::Hasher;
use trie::MemoryDB;
use heapsize::HeapSizeOf;

/// Light client backend.
pub struct Backend<S, F> {
	blockchain: Arc<Blockchain<S, F>>,
}

/// Light block (header and justification) import operation.
pub struct ImportOperation<Block: BlockT, S, F> {
	header: Option<Block::Header>,
	authorities: Option<Vec<AuthorityId>>,
	leaf_state: NewBlockState,
	_phantom: ::std::marker::PhantomData<(S, F)>,
}

/// On-demand state.
pub struct OnDemandState<Block: BlockT, S, F> {
	fetcher: Weak<F>,
	blockchain: Weak<Blockchain<S, F>>,
	block: Block::Hash,
	cached_header: RwLock<Option<Block::Header>>,
}

impl<S, F> Backend<S, F> {
	/// Create new light backend.
	pub fn new(blockchain: Arc<Blockchain<S, F>>) -> Self {
		Self { blockchain }
	}

	/// Get shared blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}
}

impl<S, F, Block, H> ClientBackend<Block, H> for Backend<S, F> where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher,

	H::Out: HeapSizeOf,
{
	type BlockImportOperation = ImportOperation<Block, S, F>;
	type Blockchain = Blockchain<S, F>;
	type State = OnDemandState<Block, S, F>;
	type ChangesTrieStorage = InMemoryChangesTrieStorage<H>;

	fn begin_operation(&self, _block: BlockId<Block>) -> ClientResult<Self::BlockImportOperation> {
		Ok(ImportOperation {
			header: None,
			authorities: None,
			leaf_state: NewBlockState::Normal,
			_phantom: Default::default(),
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> ClientResult<()> {
		let header = operation.header.expect("commit is called after set_block_data; set_block_data sets header; qed");
		self.blockchain.storage().import_header(
			header,
			operation.authorities,
			operation.leaf_state,
		)
	}

	fn finalize_block(&self, block: BlockId<Block>) -> ClientResult<()> {
		self.blockchain.storage().finalize_header(block)
	}

	fn blockchain(&self) -> &Blockchain<S, F> {
		&self.blockchain
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		None
	}

	fn state_at(&self, block: BlockId<Block>) -> ClientResult<Self::State> {
		let block_hash = match block {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.blockchain.hash(n).unwrap_or_default(),
		};

		Ok(OnDemandState {
			fetcher: self.blockchain.fetcher(),
			blockchain: Arc::downgrade(&self.blockchain),
			block: block_hash.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", block)))?,
			cached_header: RwLock::new(None),
		})
	}

	fn revert(&self, _n: NumberFor<Block>) -> ClientResult<NumberFor<Block>> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn insert_aux<'a, 'b: 'a, 'c: 'a, I: IntoIterator<Item=&'a (&'c [u8], &'c [u8])>, D: IntoIterator<Item=&'a &'b [u8]>>(&self, _insert: I, _delete: D) -> ClientResult<()> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn get_aux(&self, _key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}
}

impl<S, F, Block, H> RemoteBackend<Block, H> for Backend<S, F>
where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher,
	H::Out: HeapSizeOf,

{}

impl<S, F, Block, H> BlockImportOperation<Block, H> for ImportOperation<Block, S, F>
where
	Block: BlockT,
	F: Fetcher<Block>,
	S: BlockchainStorage<Block>,
	H: Hasher,

{
	type State = OnDemandState<Block, S, F>;

	fn state(&self) -> ClientResult<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		_body: Option<Vec<Block::Extrinsic>>,
		_justification: Option<Justification>,
		state: NewBlockState,
	) -> ClientResult<()> {
		self.leaf_state = state;
		self.header = Some(header);
		Ok(())
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		self.authorities = Some(authorities);
	}

	fn update_storage(&mut self, _update: <Self::State as StateBackend<H>>::Transaction) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn update_changes_trie(&mut self, _update: MemoryDB<H>) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, _iter: I) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}
}

impl<Block, S, F, H> StateBackend<H> for OnDemandState<Block, S, F>
	where
		Block: BlockT,
		S: BlockchainStorage<Block>,
		F: Fetcher<Block>,
		H: Hasher,

{
	type Error = ClientError;
	type Transaction = ();
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		let mut header = self.cached_header.read().clone();
		if header.is_none() {
			let cached_header = self.blockchain.upgrade()
				.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", self.block)).into())
				.and_then(|blockchain| blockchain.expect_header(BlockId::Hash(self.block)))?;
			header = Some(cached_header.clone());
			*self.cached_header.write() = Some(cached_header);
		}

		self.fetcher.upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				header: header.expect("if block above guarantees that header is_some(); qed"),
				key: key.to_vec(),
				retry_count: None,
			})
			.into_future().wait()
	}

	fn child_storage(&self, _storage_key: &[u8], _key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn for_keys_with_prefix<A: FnMut(&[u8])>(&self, _prefix: &[u8], _action: A) {
		// whole state is not available on light node
	}

	fn for_keys_in_child_storage<A: FnMut(&[u8])>(&self, _storage_key: &[u8], _action: A) {
		// whole state is not available on light node
	}

	fn storage_root<I>(&self, _delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		(H::Out::default(), ())
	}

	fn child_storage_root<I>(&self, _key: &[u8], _delta: I) -> (Vec<u8>, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		(H::Out::default().as_ref().to_vec(), ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}

	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		None
	}
}
