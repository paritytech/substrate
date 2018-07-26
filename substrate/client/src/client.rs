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

//! Substrate Client

use std::sync::Arc;
use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use primitives::AuthorityId;
use runtime_primitives::{bft::Justification, generic::{BlockId, SignedBlock, Block as RuntimeBlock}};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Zero, One, As, NumberFor};
use runtime_primitives::BuildStorage;
use primitives::storage::{StorageKey, StorageData};
use codec::Decode;
use state_machine::{Ext, OverlayedChanges, Backend as StateBackend, CodeExecutor, ExecutionStrategy, ExecutionManager};

use backend::{self, BlockImportOperation};
use blockchain::{self, Info as ChainInfo, Backend as ChainBackend, HeaderBackend as ChainHeaderBackend};
use call_executor::{CallExecutor, LocalCallExecutor};
use executor::{RuntimeVersion, RuntimeInfo};
use {error, in_mem, block_builder, runtime_io, bft, genesis};

/// Type that implements `futures::Stream` of block import events.
pub type BlockchainEventStream<Block> = mpsc::UnboundedReceiver<BlockImportNotification<Block>>;

/// Substrate Client
pub struct Client<B, E, Block> where Block: BlockT {
	backend: Arc<B>,
	executor: E,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<BlockImportNotification<Block>>>>,
	import_lock: Mutex<()>,
	importing_block: RwLock<Option<Block::Hash>>, // holds the block hash currently being imported. TODO: replace this with block queue
	execution_strategy: ExecutionStrategy,
}

/// A source of blockchain evenets.
pub trait BlockchainEvents<Block: BlockT> {
	/// Get block import event stream.
	fn import_notification_stream(&self) -> mpsc::UnboundedReceiver<BlockImportNotification<Block>>;
}

/// Chain head information.
pub trait ChainHead<Block: BlockT> {
	/// Get best block header.
	fn best_block_header(&self) -> Result<<Block as BlockT>::Header, error::Error>;
}

/// Client info
// TODO: split queue info from chain info and amalgamate into single struct.
#[derive(Debug)]
pub struct ClientInfo<Block: BlockT> {
	/// Best block hash.
	pub chain: ChainInfo<Block>,
	/// Best block number in the queue.
	pub best_queued_number: Option<<<Block as BlockT>::Header as HeaderT>::Number>,
	/// Best queued block hash.
	pub best_queued_hash: Option<Block::Hash>,
}

/// Block import result.
#[derive(Debug)]
pub enum ImportResult {
	/// Added to the import queue.
	Queued,
	/// Already in the import queue.
	AlreadyQueued,
	/// Already in the blockchain.
	AlreadyInChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Block parent is not in the chain.
	UnknownParent,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Added to the import queue.
	Queued,
	/// Already in the blockchain.
	InChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Not in the queue or the blockchain.
	Unknown,
}

/// Block data origin.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockOrigin {
	/// Genesis block built into the client.
	Genesis,
	/// Block is part of the initial sync with the network.
	NetworkInitialSync,
	/// Block was broadcasted on the network.
	NetworkBroadcast,
	/// Block that was received from the network and validated in the consensus process.
	ConsensusBroadcast,
	/// Block that was collated by this node.
	Own,
	/// Block was imported from a file.
	File,
}

/// Summary of an imported block
#[derive(Clone, Debug)]
pub struct BlockImportNotification<Block: BlockT> {
	/// Imported block header hash.
	pub hash: Block::Hash,
	/// Imported block origin.
	pub origin: BlockOrigin,
	/// Imported block header.
	pub header: Block::Header,
	/// Is this the new best block.
	pub is_new_best: bool,
}

/// A header paired with a justification which has already been checked.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct JustifiedHeader<Block: BlockT> {
	header: <Block as BlockT>::Header,
	justification: ::bft::Justification<Block::Hash>,
}

impl<Block: BlockT> JustifiedHeader<Block> {
	/// Deconstruct the justified header into parts.
	pub fn into_inner(self) -> (<Block as BlockT>::Header, ::bft::Justification<Block::Hash>) {
		(self.header, self.justification)
	}
}

/// Create an instance of in-memory client.
pub fn new_in_mem<E, Block, S>(
	executor: E,
	genesis_storage: S,
) -> error::Result<Client<in_mem::Backend<Block>, LocalCallExecutor<in_mem::Backend<Block>, E>, Block>>
	where
		E: CodeExecutor + RuntimeInfo,
		S: BuildStorage,
		Block: BlockT,
{
	let backend = Arc::new(in_mem::Backend::new());
	let executor = LocalCallExecutor::new(backend.clone(), executor);
	Client::new(backend, executor, genesis_storage, ExecutionStrategy::NativeWhenPossible)
}

impl<B, E, Block> Client<B, E, Block> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	/// Creates new Substrate Client with given blockchain and code executor.
	pub fn new<S: BuildStorage>(
		backend: Arc<B>,
		executor: E,
		build_genesis_storage: S,
		execution_strategy: ExecutionStrategy,
	) -> error::Result<Self> {
		if backend.blockchain().header(BlockId::Number(Zero::zero()))?.is_none() {
			let genesis_storage = build_genesis_storage.build_storage()?;
			let genesis_block = genesis::construct_genesis_block::<Block>(&genesis_storage);
			info!("Initialising Genesis block/state (state: {}, header-hash: {})", genesis_block.header().state_root(), genesis_block.header().hash());
			let mut op = backend.begin_operation(BlockId::Hash(Default::default()))?;
			op.reset_storage(genesis_storage.into_iter())?;
			op.set_block_data(genesis_block.deconstruct().0, Some(vec![]), None, true)?;
			backend.commit_operation(op)?;
		}
		Ok(Client {
			backend,
			executor,
			import_notification_sinks: Mutex::new(Vec::new()),
			import_lock: Mutex::new(()),
			importing_block: RwLock::new(None),
			execution_strategy,
		})
	}

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, block: &BlockId<Block>) -> error::Result<B::State> {
		self.backend.state_at(*block)
	}

	/// Expose backend reference. To be used in tests only
	pub fn backend(&self) -> &Arc<B> {
		&self.backend
	}

	/// Return single storage entry of contract under given address in state in a block of given hash.
	pub fn storage(&self, id: &BlockId<Block>, key: &StorageKey) -> error::Result<StorageData> {
		Ok(StorageData(self.state_at(id)?
			.storage(&key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
			.ok_or_else(|| error::ErrorKind::NoValueForKey(key.0.clone()))?
			.to_vec()))
	}

	/// Get the code at a given block.
	pub fn code_at(&self, id: &BlockId<Block>) -> error::Result<Vec<u8>> {
		self.storage(id, &StorageKey(b":code".to_vec())).map(|data| data.0)
	}

	/// Get the set of authorities at a given block.
	pub fn authorities_at(&self, id: &BlockId<Block>) -> error::Result<Vec<AuthorityId>> {
		self.executor.call(id, "authorities", &[])
			.and_then(|r| Vec::<AuthorityId>::decode(&mut &r.return_data[..])
				.ok_or(error::ErrorKind::AuthLenInvalid.into()))
	}

	/// Get the RuntimeVersion at a given block.
	pub fn runtime_version_at(&self, id: &BlockId<Block>) -> error::Result<RuntimeVersion> {
		// TODO: Post Poc-2 return an error if version is missing
		self.executor.runtime_version(id)
	}

	/// Get call executor reference.
	pub fn executor(&self) -> &E {
		&self.executor
	}

	/// Execute a call to a contract on top of state in a block of given hash
	/// AND returning execution proof.
	///
	/// No changes are made.
	pub fn execution_proof(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, Vec<Vec<u8>>)> {
		self.state_at(id).and_then(|state| self.executor.prove_at_state(state, &mut Default::default(), method, call_data))
	}

	/// Set up the native execution environment to call into a native runtime code.
	pub fn using_environment<F: FnOnce() -> T, T>(
		&self, f: F
	) -> error::Result<T> {
		self.using_environment_at(&BlockId::Number(self.info()?.chain.best_number), &mut Default::default(), f)
	}

	/// Set up the native execution environment to call into a native runtime code.
	pub fn using_environment_at<F: FnOnce() -> T, T>(
		&self,
		id: &BlockId<Block>,
		overlay: &mut OverlayedChanges,
		f: F
	) -> error::Result<T> {
		Ok(runtime_io::with_externalities(&mut Ext::new(overlay, &self.state_at(id)?), f))
	}

	/// Create a new block, built on the head of the chain.
	pub fn new_block(&self) -> error::Result<block_builder::BlockBuilder<B, E, Block>> where E: Clone {
		block_builder::BlockBuilder::new(self)
	}

	/// Create a new block, built on top of `parent`.
	pub fn new_block_at(&self, parent: &BlockId<Block>) -> error::Result<block_builder::BlockBuilder<B, E, Block>> where E: Clone {
		block_builder::BlockBuilder::at_block(parent, &self)
	}

	/// Check a header's justification.
	pub fn check_justification(
		&self,
		header: <Block as BlockT>::Header,
		justification: ::bft::UncheckedJustification<Block::Hash>,
	) -> error::Result<JustifiedHeader<Block>> {
		let parent_hash = header.parent_hash().clone();
		let authorities = self.authorities_at(&BlockId::Hash(parent_hash))?;
		let just = ::bft::check_justification::<Block>(&authorities[..], parent_hash, justification)
			.map_err(|_|
				error::ErrorKind::BadJustification(
					format!("{}", header.hash())
				)
			)?;
		Ok(JustifiedHeader {
			header,
			justification: just,
		})
	}

	/// Queue a block for import.
	pub fn import_block(
		&self,
		origin: BlockOrigin,
		header: JustifiedHeader<Block>,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
	) -> error::Result<ImportResult> {
		let (header, justification) = header.into_inner();
		let parent_hash = header.parent_hash().clone();
		match self.backend.blockchain().status(BlockId::Hash(parent_hash))? {
			blockchain::BlockStatus::InChain => {},
			blockchain::BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
		}
		let hash = header.hash();
		let _import_lock = self.import_lock.lock();
		let height: u64 = header.number().as_();
		*self.importing_block.write() = Some(hash);
		let result = self.execute_and_import_block(origin, hash, header, justification, body);
		*self.importing_block.write() = None;
		telemetry!("block.import";
			"height" => height,
			"best" => ?hash,
			"origin" => ?origin
		);
		result
	}

	fn execute_and_import_block(
		&self,
		origin: BlockOrigin,
		hash: Block::Hash,
		header: Block::Header,
		justification: bft::Justification<Block::Hash>,
		body: Option<Vec<Block::Extrinsic>>,
	) -> error::Result<ImportResult> {
		let parent_hash = header.parent_hash().clone();
		match self.backend.blockchain().status(BlockId::Hash(hash))? {
			blockchain::BlockStatus::InChain => return Ok(ImportResult::AlreadyInChain),
			blockchain::BlockStatus::Unknown => {},
		}

		let mut transaction = self.backend.begin_operation(BlockId::Hash(parent_hash))?;
		let storage_update = match transaction.state()? {
			Some(transaction_state) => {
				let mut overlay = Default::default();
				let mut r = self.executor.call_at_state(
					transaction_state,
					&mut overlay,
					"execute_block",
					&<Block as BlockT>::new(header.clone(), body.clone().unwrap_or_default()).encode(),
					match (origin, self.execution_strategy) {
						(BlockOrigin::NetworkInitialSync, _) | (_, ExecutionStrategy::NativeWhenPossible) =>
							ExecutionManager::NativeWhenPossible,
						(_, ExecutionStrategy::AlwaysWasm) => ExecutionManager::AlwaysWasm,
						_ => ExecutionManager::Both(|wasm_result, native_result| {
							warn!("Consensus error between wasm and native block execution at block {}", hash);
							warn!("   Header {:?}", header);
							warn!("   Native result {:?}", native_result);
							warn!("   Wasm result {:?}", wasm_result);
							telemetry!("block.execute.consensus_failure";
								"hash" => ?hash,
								"origin" => ?origin,
								"header" => ?header
							);
							wasm_result
						}),
					},
				);
				let (_, storage_update) = r?;
				Some(storage_update)
			},
			None => None,
		};

		let is_new_best = header.number() == &(self.backend.blockchain().info()?.best_number + One::one());
		trace!("Imported {}, (#{}), best={}, origin={:?}", hash, header.number(), is_new_best, origin);
		let unchecked: bft::UncheckedJustification<_> = justification.uncheck().into();
		transaction.set_block_data(header.clone(), body, Some(unchecked.into()), is_new_best)?;
		if let Some(storage_update) = storage_update {
			transaction.update_storage(storage_update)?;
		}
		self.backend.commit_operation(transaction)?;
		if origin == BlockOrigin::NetworkBroadcast || origin == BlockOrigin::Own || origin == BlockOrigin::ConsensusBroadcast {
			let notification = BlockImportNotification::<Block> {
				hash: hash,
				origin: origin,
				header: header,
				is_new_best: is_new_best,
			};
			self.import_notification_sinks.lock()
				.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
		}
		Ok(ImportResult::Queued)
	}

	/// Attempts to revert the chain by `n` blocks. Returns the number of blocks that were
	/// successfully reverted.
	pub fn revert(&self, n: NumberFor<Block>) -> error::Result<NumberFor<Block>> {
		Ok(self.backend.revert(n)?)
	}

	/// Get blockchain info.
	pub fn info(&self) -> error::Result<ClientInfo<Block>> {
		let info = self.backend.blockchain().info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(ClientInfo {
			chain: info,
			best_queued_hash: None,
			best_queued_number: None,
		})
	}

	/// Get block status.
	pub fn block_status(&self, id: &BlockId<Block>) -> error::Result<BlockStatus> {
		// TODO: more efficient implementation
		if let BlockId::Hash(ref h) = id {
			if self.importing_block.read().as_ref().map_or(false, |importing| h == importing) {
				return Ok(BlockStatus::Queued);
			}
		}
		match self.backend.blockchain().header(*id).map_err(|e| error::Error::from_blockchain(Box::new(e)))?.is_some() {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: <<Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Convert an arbitrary block ID into a block hash.
	pub fn block_hash_from_id(&self, id: &BlockId<Block>) -> error::Result<Option<Block::Hash>> {
		match *id {
			BlockId::Hash(h) => Ok(Some(h)),
			BlockId::Number(n) => self.block_hash(n),
		}
	}

	/// Convert an arbitrary block ID into a block hash.
	pub fn block_number_from_id(&self, id: &BlockId<Block>) -> error::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		match *id {
			BlockId::Hash(_) => Ok(self.header(id)?.map(|h| h.number().clone())),
			BlockId::Number(n) => Ok(Some(n)),
		}
	}

	/// Get block header by id.
	pub fn header(&self, id: &BlockId<Block>) -> error::Result<Option<<Block as BlockT>::Header>> {
		self.backend.blockchain().header(*id)
	}

	/// Get block body by id.
	pub fn body(&self, id: &BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.backend.blockchain().body(*id)
	}

	/// Get block justification set by id.
	pub fn justification(&self, id: &BlockId<Block>) -> error::Result<Option<Justification<Block::Hash>>> {
		self.backend.blockchain().justification(*id)
	}

	/// Get full block by id.
	pub fn block(&self, id: &BlockId<Block>) -> error::Result<Option<SignedBlock<Block::Header, Block::Extrinsic, Block::Hash>>> {
		Ok(match (self.header(id)?, self.body(id)?, self.justification(id)?) {
			(Some(header), Some(extrinsics), Some(justification)) =>
				Some(SignedBlock { block: RuntimeBlock { header, extrinsics }, justification }),
			_ => None,
		})
	}

	/// Get best block header.
	pub fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		let info = self.backend.blockchain().info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(self.header(&BlockId::Hash(info.best_hash))?.expect("Best block header must always exist"))
	}
}

impl<B, E, Block> bft::BlockImport<Block> for Client<B, E, Block>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
{
	fn import_block(&self, block: Block, justification: ::bft::Justification<Block::Hash>) {
		let (header, extrinsics) = block.deconstruct();
		let justified_header = JustifiedHeader {
			header: header,
			justification,
		};

		let _ = self.import_block(BlockOrigin::ConsensusBroadcast, justified_header, Some(extrinsics));
	}
}

impl<B, E, Block> bft::Authorities<Block> for Client<B, E, Block>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
{
	fn authorities(&self, at: &BlockId<Block>) -> Result<Vec<AuthorityId>, bft::Error> {
		let on_chain_version: Result<_, bft::Error> = self.runtime_version_at(at)
			.map_err(|e| { trace!("Error getting runtime version {:?}", e); bft::ErrorKind::RuntimeVersionMissing.into() });
		let on_chain_version = on_chain_version?;
		let native_version: Result<_, bft::Error> = self.executor.native_runtime_version()
			.ok_or_else(|| bft::ErrorKind::NativeRuntimeMissing.into());
		let native_version = native_version?;
		if !on_chain_version.can_author_with(&native_version) {
			return Err(bft::ErrorKind::IncompatibleAuthoringRuntime(on_chain_version, native_version).into())
		}
		self.authorities_at(at).map_err(|_| {
			let descriptor = format!("{:?}", at);
			bft::ErrorKind::StateUnavailable(descriptor).into()
		})
	}
}

impl<B, E, Block> BlockchainEvents<Block> for Client<B, E, Block>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
{
	/// Get block import event stream.
	fn import_notification_stream(&self) -> mpsc::UnboundedReceiver<BlockImportNotification<Block>> {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}
}

impl<B, E, Block> ChainHead<Block> for Client<B, E, Block>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
{
	fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		Client::best_block_header(self)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Encode;
	use keyring::Keyring;
	use test_client::{self, TestClient};
	use test_client::client::BlockOrigin;
	use test_client::runtime as test_runtime;
	use test_client::runtime::{Transfer, Extrinsic};

	#[test]
	fn client_initialises_from_genesis_ok() {
		let client = test_client::new();

		assert_eq!(client.using_environment(|| test_runtime::system::balance_of(Keyring::Alice.to_raw_public().into())).unwrap(), 1000);
		assert_eq!(client.using_environment(|| test_runtime::system::balance_of(Keyring::Ferdie.to_raw_public().into())).unwrap(), 0);
	}

	#[test]
	fn authorities_call_works() {
		let client = test_client::new();

		assert_eq!(client.info().unwrap().chain.best_number, 0);
		assert_eq!(client.authorities_at(&BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.to_raw_public().into(),
			Keyring::Bob.to_raw_public().into(),
			Keyring::Charlie.to_raw_public().into()
		]);
	}

	#[test]
	fn block_builder_works_with_no_transactions() {
		let client = test_client::new();

		let builder = client.new_block().unwrap();

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
	}

	fn sign_tx(tx: Transfer) -> Extrinsic {
		let signature = Keyring::from_raw_public(tx.from.0.clone()).unwrap().sign(&tx.encode()).into();
		Extrinsic { transfer: tx, signature }
	}

	#[test]
	fn block_builder_works_with_transactions() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push(sign_tx(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		})).unwrap();

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap() != client.state_at(&BlockId::Number(0)).unwrap());
		assert_eq!(client.using_environment(|| test_runtime::system::balance_of(Keyring::Alice.to_raw_public().into())).unwrap(), 958);
		assert_eq!(client.using_environment(|| test_runtime::system::balance_of(Keyring::Ferdie.to_raw_public().into())).unwrap(), 42);
	}

	#[test]
	fn block_builder_does_not_include_invalid() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push(sign_tx(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		})).unwrap();

		assert!(builder.push(sign_tx(Transfer {
			from: Keyring::Eve.to_raw_public().into(),
			to: Keyring::Alice.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		})).is_err());

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap() != client.state_at(&BlockId::Number(0)).unwrap());
		assert_eq!(client.body(&BlockId::Number(1)).unwrap().unwrap().len(), 1)
	}
}
