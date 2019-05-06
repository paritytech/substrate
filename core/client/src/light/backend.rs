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

//! Light client backend. Only stores headers and justifications of blocks.
//! Everything else is requested from full nodes on demand.

use std::collections::HashMap;
use std::sync::{Arc, Weak};
use futures::{Future, IntoFuture};
use parking_lot::RwLock;

use runtime_primitives::{generic::BlockId, Justification, StorageOverlay, ChildrenStorageOverlay};
use state_machine::{Backend as StateBackend, TrieBackend, backend::InMemory as InMemoryState};
use runtime_primitives::traits::{Block as BlockT, NumberFor, Zero, Header};
use crate::in_mem::{self, check_genesis_storage};
use crate::backend::{AuxStore, Backend as ClientBackend, BlockImportOperation, RemoteBackend, NewBlockState};
use crate::blockchain::HeaderBackend as BlockchainHeaderBackend;
use crate::error::{Error as ClientError, Result as ClientResult};
use crate::light::blockchain::{Blockchain, Storage as BlockchainStorage};
use crate::light::fetcher::{Fetcher, RemoteReadRequest};
use hash_db::Hasher;
use trie::MemoryDB;
use consensus::well_known_cache_keys;

const IN_MEMORY_EXPECT_PROOF: &str = "InMemory state backend has Void error type and always suceeds; qed";

/// Light client backend.
pub struct Backend<S, F, H> {
	blockchain: Arc<Blockchain<S, F>>,
	genesis_state: RwLock<Option<InMemoryState<H>>>,
}

/// Light block (header and justification) import operation.
pub struct ImportOperation<Block: BlockT, S, F, H> {
	header: Option<Block::Header>,
	cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	leaf_state: NewBlockState,
	aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<BlockId<Block>>,
	set_head: Option<BlockId<Block>>,
	storage_update: Option<InMemoryState<H>>,
	_phantom: ::std::marker::PhantomData<(S, F)>,
}

/// On-demand state.
pub struct OnDemandState<Block: BlockT, S, F> {
	fetcher: Weak<F>,
	blockchain: Weak<Blockchain<S, F>>,
	block: Block::Hash,
	cached_header: RwLock<Option<Block::Header>>,
}

/// On-demand or in-memory genesis state.
pub enum OnDemandOrGenesisState<Block: BlockT, S, F, H> {
	/// On-demand state - storage values are fetched from remote nodes.
	OnDemand(OnDemandState<Block, S, F>),
	/// Genesis state - storage values are stored in-memory.
	Genesis(InMemoryState<H>),
}

impl<S, F, H> Backend<S, F, H> {
	/// Create new light backend.
	pub fn new(blockchain: Arc<Blockchain<S, F>>) -> Self {
		Self {
			blockchain,
			genesis_state: RwLock::new(None),
		}
	}

	/// Get shared blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}
}

impl<S: AuxStore, F, H> AuxStore for Backend<S, F, H> {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> ClientResult<()> {
		self.blockchain.storage().insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		self.blockchain.storage().get_aux(key)
	}
}

impl<S, F, Block, H> ClientBackend<Block, H> for Backend<S, F, H> where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	type BlockImportOperation = ImportOperation<Block, S, F, H>;
	type Blockchain = Blockchain<S, F>;
	type State = OnDemandOrGenesisState<Block, S, F, H>;
	type ChangesTrieStorage = in_mem::ChangesTrieStorage<H>;

	fn begin_operation(&self) -> ClientResult<Self::BlockImportOperation> {
		Ok(ImportOperation {
			header: None,
			cache: Default::default(),
			leaf_state: NewBlockState::Normal,
			aux_ops: Vec::new(),
			finalized_blocks: Vec::new(),
			set_head: None,
			storage_update: None,
			_phantom: Default::default(),
		})
	}

	fn begin_state_operation(
		&self,
		_operation: &mut Self::BlockImportOperation,
		_block: BlockId<Block>
	) -> ClientResult<()> {
		Ok(())
	}

	fn commit_operation(&self, mut operation: Self::BlockImportOperation) -> ClientResult<()> {
		if !operation.finalized_blocks.is_empty() {
			for block in operation.finalized_blocks {
				self.blockchain.storage().finalize_header(block)?;
			}
		}

		if let Some(header) = operation.header {
			let is_genesis_import = header.number().is_zero();
			self.blockchain.storage().import_header(
				header,
				operation.cache,
				operation.leaf_state,
				operation.aux_ops,
			)?;

			// when importing genesis block => remember its state
			if is_genesis_import {
				*self.genesis_state.write() = operation.storage_update.take();
			}
		} else {
			for (key, maybe_val) in operation.aux_ops {
				match maybe_val {
					Some(val) => self.blockchain.storage().insert_aux(
						&[(&key[..], &val[..])],
						::std::iter::empty(),
					)?,
					None => self.blockchain.storage().insert_aux(::std::iter::empty(), &[&key[..]])?,
				}
			}
		}

		if let Some(set_head) = operation.set_head {
			self.blockchain.storage().set_head(set_head)?;
		}

		Ok(())
	}

	fn finalize_block(&self, block: BlockId<Block>, _justification: Option<Justification>) -> ClientResult<()> {
		self.blockchain.storage().finalize_header(block)
	}

	fn blockchain(&self) -> &Blockchain<S, F> {
		&self.blockchain
	}

	fn used_state_cache_size(&self) -> Option<usize> {
		None
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		None
	}

	fn state_at(&self, block: BlockId<Block>) -> ClientResult<Self::State> {
		let block_number = self.blockchain.expect_block_number_from_id(&block)?;

		// special case for genesis block
		if block_number.is_zero() {
			if let Some(genesis_state) = self.genesis_state.read().clone() {
				return Ok(OnDemandOrGenesisState::Genesis(genesis_state));
			}
		}

		// else create on-demand state
		let block_hash = self.blockchain.expect_block_hash_from_id(&block)?;
		Ok(OnDemandOrGenesisState::OnDemand(OnDemandState {
			fetcher: self.blockchain.fetcher(),
			blockchain: Arc::downgrade(&self.blockchain),
			block: block_hash,
			cached_header: RwLock::new(None),
		}))
	}

	fn revert(&self, _n: NumberFor<Block>) -> ClientResult<NumberFor<Block>> {
		Err(ClientError::NotAvailableOnLightClient.into())
	}
}

impl<S, F, Block, H> RemoteBackend<Block, H> for Backend<S, F, H>
where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	fn is_local_state_available(&self, block: &BlockId<Block>) -> bool {
		self.genesis_state.read().is_some()
			&& self.blockchain.expect_block_number_from_id(block)
				.map(|num| num.is_zero())
				.unwrap_or(false)
	}
}

impl<S, F, Block, H> BlockImportOperation<Block, H> for ImportOperation<Block, S, F, H>
where
	Block: BlockT,
	F: Fetcher<Block>,
	S: BlockchainStorage<Block>,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	type State = OnDemandOrGenesisState<Block, S, F, H>;

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

	fn update_cache(&mut self, cache: HashMap<well_known_cache_keys::Id, Vec<u8>>) {
		self.cache = cache;
	}

	fn update_db_storage(&mut self, _update: <Self::State as StateBackend<H>>::Transaction) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn update_changes_trie(&mut self, _update: MemoryDB<H>) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn reset_storage(&mut self, top: StorageOverlay, children: ChildrenStorageOverlay) -> ClientResult<H::Out> {
		check_genesis_storage(&top, &children)?;

		// this is only called when genesis block is imported => shouldn't be performance bottleneck
		let mut storage: HashMap<Option<Vec<u8>>, StorageOverlay> = HashMap::new();
		storage.insert(None, top);
		for (child_key, child_storage) in children {
			storage.insert(Some(child_key), child_storage);
		}
		let storage_update: InMemoryState<H> = storage.into();
		let (storage_root, _) = storage_update.storage_root(::std::iter::empty());
		self.storage_update = Some(storage_update);

		Ok(storage_root)
	}

	fn insert_aux<I>(&mut self, ops: I) -> ClientResult<()>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.aux_ops.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(&mut self, _update: Vec<(Vec<u8>, Option<Vec<u8>>)>) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn mark_finalized(&mut self, block: BlockId<Block>, _justification: Option<Justification>) -> ClientResult<()> {
		self.finalized_blocks.push(block);
		Ok(())
	}

	fn mark_head(&mut self, block: BlockId<Block>) -> ClientResult<()> {
		self.set_head = Some(block);
		Ok(())
	}
}

impl<Block, S, F, H> StateBackend<H> for OnDemandState<Block, S, F>
where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher<Out=Block::Hash>,
{
	type Error = ClientError;
	type Transaction = ();
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		let mut header = self.cached_header.read().clone();
		if header.is_none() {
			let cached_header = self.blockchain.upgrade()
				.ok_or_else(|| ClientError::UnknownBlock(format!("{}", self.block)))
				.and_then(|blockchain| blockchain.expect_header(BlockId::Hash(self.block)))?;
			header = Some(cached_header.clone());
			*self.cached_header.write() = Some(cached_header);
		}

		self.fetcher.upgrade().ok_or(ClientError::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				header: header.expect("if block above guarantees that header is_some(); qed"),
				key: key.to_vec(),
				retry_count: None,
			})
			.into_future().wait()
	}

	fn child_storage(&self, _storage_key: &[u8], _key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Err(ClientError::NotAvailableOnLightClient.into())
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

	fn child_storage_root<I>(&self, _key: &[u8], _delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		(H::Out::default().as_ref().to_vec(), true, ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}

	fn keys(&self, _prefix: &Vec<u8>) -> Vec<Vec<u8>> {
		// whole state is not available on light node
		Vec::new()
	}

	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		None
	}
}

impl<Block, S, F, H> StateBackend<H> for OnDemandOrGenesisState<Block, S, F, H>
where
	Block: BlockT,
	F: Fetcher<Block>,
	S: BlockchainStorage<Block>,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	type Error = ClientError;
	type Transaction = ();
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::storage(state, key),
			OnDemandOrGenesisState::Genesis(ref state) =>
				Ok(state.storage(key).expect(IN_MEMORY_EXPECT_PROOF)),
		}
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::child_storage(state, storage_key, key),
			OnDemandOrGenesisState::Genesis(ref state) =>
				Ok(state.child_storage(storage_key, key).expect(IN_MEMORY_EXPECT_PROOF)),
		}
	}

	fn for_keys_with_prefix<A: FnMut(&[u8])>(&self, prefix: &[u8], action: A) {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::for_keys_with_prefix(state, prefix, action),
			OnDemandOrGenesisState::Genesis(ref state) => state.for_keys_with_prefix(prefix, action),
		}
	}

	fn for_keys_in_child_storage<A: FnMut(&[u8])>(&self, storage_key: &[u8], action: A) {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::for_keys_in_child_storage(state, storage_key, action),
			OnDemandOrGenesisState::Genesis(ref state) => state.for_keys_in_child_storage(storage_key, action),
		}
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::storage_root(state, delta),
			OnDemandOrGenesisState::Genesis(ref state) => {
				let (root, _) = state.storage_root(delta);
				(root, ())
			},
		}
	}

	fn child_storage_root<I>(&self, key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::child_storage_root(state, key, delta),
			OnDemandOrGenesisState::Genesis(ref state) => {
				let (root, is_equal, _) = state.child_storage_root(key, delta);
				(root, is_equal, ())
			},
		}
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::pairs(state),
			OnDemandOrGenesisState::Genesis(ref state) => state.pairs(),
		}
	}

	fn keys(&self, prefix: &Vec<u8>) -> Vec<Vec<u8>> {
		match *self {
			OnDemandOrGenesisState::OnDemand(ref state) =>
				StateBackend::<H>::keys(state, prefix),
			OnDemandOrGenesisState::Genesis(ref state) => state.keys(prefix),
		}
	}

	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		match self {
			OnDemandOrGenesisState::OnDemand(state) => state.try_into_trie_backend(),
			OnDemandOrGenesisState::Genesis(state) => state.try_into_trie_backend(),
		}
	}
}

#[cfg(test)]
mod tests {
	use primitives::Blake2Hasher;
	use test_client::{self, runtime::Block};
	use crate::backend::NewBlockState;
	use crate::light::blockchain::tests::{DummyBlockchain, DummyStorage};
	use super::*;

	#[test]
	fn local_state_is_created_when_genesis_state_is_available() {
		let def = Default::default();
		let header0 = test_client::runtime::Header::new(0, def, def, def, Default::default());

		let backend: Backend<_, _, Blake2Hasher> = Backend::new(Arc::new(DummyBlockchain::new(DummyStorage::new())));
		let mut op = backend.begin_operation().unwrap();
		op.set_block_data(header0, None, None, NewBlockState::Final).unwrap();
		op.reset_storage(Default::default(), Default::default()).unwrap();
		backend.commit_operation(op).unwrap();

		match backend.state_at(BlockId::Number(0)).unwrap() {
			OnDemandOrGenesisState::Genesis(_) => (),
			_ => panic!("unexpected state"),
		}
	}

	#[test]
	fn remote_state_is_created_when_genesis_state_is_inavailable() {
		let backend: Backend<_, _, Blake2Hasher> = Backend::new(Arc::new(DummyBlockchain::new(DummyStorage::new())));

		match backend.state_at(BlockId::Number(0)).unwrap() {
			OnDemandOrGenesisState::OnDemand(_) => (),
			_ => panic!("unexpected state"),
		}
	}

	#[test]
	fn light_aux_store_is_updated_via_non_importing_op() {
		let backend = Backend::new(Arc::new(DummyBlockchain::new(DummyStorage::new())));
		let mut op = ClientBackend::<Block, Blake2Hasher>::begin_operation(&backend).unwrap();
		BlockImportOperation::<Block, Blake2Hasher>::insert_aux(&mut op, vec![(vec![1], Some(vec![2]))]).unwrap();
		ClientBackend::<Block, Blake2Hasher>::commit_operation(&backend, op).unwrap();

		assert_eq!(AuxStore::get_aux(&backend, &[1]).unwrap(), Some(vec![2]));
	}
}
