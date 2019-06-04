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

//! Light client call executor. Executes methods on remote full nodes, fetching
//! execution proof and checking it locally.

use std::{
	collections::HashSet, sync::Arc, panic::UnwindSafe, result,
	marker::PhantomData, cell::RefCell, rc::Rc,
};
use futures::{IntoFuture, Future};

use parity_codec::{Encode, Decode};
use primitives::{offchain, H256, Blake2Hasher, convert_hash, NativeOrEncoded};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{One, Block as BlockT, Header as HeaderT};
use state_machine::{
	self, Backend as StateBackend, CodeExecutor, OverlayedChanges,
	ExecutionStrategy, create_proof_check_backend,
	execution_proof_check_on_trie_backend, ExecutionManager, NeverOffchainExt
};
use hash_db::Hasher;

use crate::runtime_api::{ProofRecorder, InitializeBlock};
use crate::backend::RemoteBackend;
use crate::blockchain::Backend as ChainBackend;
use crate::call_executor::CallExecutor;
use crate::error::{Error as ClientError, Result as ClientResult};
use crate::light::fetcher::{Fetcher, RemoteCallRequest};
use executor::{RuntimeVersion, NativeVersion};
use trie::MemoryDB;

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F> {
	blockchain: Arc<B>,
	fetcher: Arc<F>,
}

/// Remote or local call executor.
///
/// Calls are executed locally if state is available locally. Otherwise, calls
/// are redirected to remote call executor.
pub struct RemoteOrLocalCallExecutor<Block: BlockT<Hash=H256>, B, R, L> {
	backend: Arc<B>,
	remote: R,
	local: L,
	_block: PhantomData<Block>,
}

impl<B, F> Clone for RemoteCallExecutor<B, F> {
	fn clone(&self) -> Self {
		RemoteCallExecutor {
			blockchain: self.blockchain.clone(),
			fetcher: self.fetcher.clone(),
		}
	}
}

impl<B, F> RemoteCallExecutor<B, F> {
	/// Creates new instance of remote call executor.
	pub fn new(blockchain: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { blockchain, fetcher }
	}
}

impl<B, F, Block> CallExecutor<Block, Blake2Hasher> for RemoteCallExecutor<B, F>
where
	Block: BlockT<Hash=H256>,
	B: ChainBackend<Block>,
	F: Fetcher<Block>,
	Block::Hash: Ord,
{
	type Error = ClientError;

	fn call<
		O: offchain::Externalities,
	>(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		_strategy: ExecutionStrategy,
		_side_effects_handler: Option<&mut O>,
	)
		-> ClientResult<Vec<u8>> {
		let block_hash = self.blockchain.expect_block_hash_from_id(id)?;
		let block_header = self.blockchain.expect_header(id.clone())?;

		self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash,
			header: block_header,
			method: method.into(),
			call_data: call_data.to_vec(),
			retry_count: None,
		}).into_future().wait()
	}

	fn contextual_call<
		'a,
		O: offchain::Externalities,
		IB: Fn() -> ClientResult<()>,
		EM: Fn(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC,
	>(
		&self,
		_initialize_block_fn: IB,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		initialize_block: InitializeBlock<'a, Block>,
		execution_manager: ExecutionManager<EM>,
		_native_call: Option<NC>,
		side_effects_handler: Option<&mut O>,
		_recorder: &Option<Rc<RefCell<ProofRecorder<Block>>>>,
	) -> ClientResult<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone {
		let block_initialized = match initialize_block {
			InitializeBlock::Do(ref init_block) => {
				init_block.borrow().is_some()
			},
			InitializeBlock::Skip => false,
		};

		// it is only possible to execute contextual call if changes are empty
		if !changes.borrow().is_empty() || block_initialized {
			return Err(ClientError::NotAvailableOnLightClient.into());
		}

		self.call(at, method, call_data, (&execution_manager).into(), side_effects_handler).map(NativeOrEncoded::Encoded)
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		let call_result = self.call(id, "Core_version", &[], ExecutionStrategy::NativeElseWasm, NeverOffchainExt::new())?;
		RuntimeVersion::decode(&mut call_result.as_slice())
			.ok_or_else(|| ClientError::VersionInvalid.into())
	}

	fn call_at_state<
		O: offchain::Externalities,
		S: StateBackend<Blake2Hasher>,
		FF: FnOnce(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str>,
	>(&self,
		_state: &S,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8],
		_m: ExecutionManager<FF>,
		_native_call: Option<NC>,
		_side_effects_handler: Option<&mut O>,
	) -> ClientResult<(NativeOrEncoded<R>, S::Transaction, Option<MemoryDB<Blake2Hasher>>)> {
		Err(ClientError::NotAvailableOnLightClient.into())
	}

	fn prove_at_trie_state<S: state_machine::TrieBackendStorage<Blake2Hasher>>(
		&self,
		_state: &state_machine::TrieBackend<S, Blake2Hasher>,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8]
	) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		Err(ClientError::NotAvailableOnLightClient.into())
	}

	fn native_runtime_version(&self) -> Option<&NativeVersion> {
		None
	}
}

impl<Block, B, R, L> Clone for RemoteOrLocalCallExecutor<Block, B, R, L>
	where
		Block: BlockT<Hash=H256>,
		B: RemoteBackend<Block, Blake2Hasher>,
		R: CallExecutor<Block, Blake2Hasher> + Clone,
		L: CallExecutor<Block, Blake2Hasher> + Clone,
{
	fn clone(&self) -> Self {
		RemoteOrLocalCallExecutor {
			backend: self.backend.clone(),
			remote: self.remote.clone(),
			local: self.local.clone(),
			_block: Default::default(),
		}
	}
}

impl<Block, B, Remote, Local> RemoteOrLocalCallExecutor<Block, B, Remote, Local>
	where
		Block: BlockT<Hash=H256>,
		B: RemoteBackend<Block, Blake2Hasher>,
		Remote: CallExecutor<Block, Blake2Hasher>,
		Local: CallExecutor<Block, Blake2Hasher>,
{
	/// Creates new instance of remote/local call executor.
	pub fn new(backend: Arc<B>, remote: Remote, local: Local) -> Self {
		RemoteOrLocalCallExecutor { backend, remote, local, _block: Default::default(), }
	}
}

impl<Block, B, Remote, Local> CallExecutor<Block, Blake2Hasher> for
	RemoteOrLocalCallExecutor<Block, B, Remote, Local>
	where
		Block: BlockT<Hash=H256>,
		B: RemoteBackend<Block, Blake2Hasher>,
		Remote: CallExecutor<Block, Blake2Hasher>,
		Local: CallExecutor<Block, Blake2Hasher>,
{
	type Error = ClientError;

	fn call<
		O: offchain::Externalities,
	>(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		side_effects_handler: Option<&mut O>,
	) -> ClientResult<Vec<u8>> {
		match self.backend.is_local_state_available(id) {
			true => self.local.call(id, method, call_data, strategy, side_effects_handler),
			false => self.remote.call(id, method, call_data, strategy, side_effects_handler),
		}
	}

	fn contextual_call<
		'a,
		O: offchain::Externalities,
		IB: Fn() -> ClientResult<()>,
		EM: Fn(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
	>(
		&self,
		initialize_block_fn: IB,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		initialize_block: InitializeBlock<'a, Block>,
		_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		side_effects_handler: Option<&mut O>,
		recorder: &Option<Rc<RefCell<ProofRecorder<Block>>>>,
	) -> ClientResult<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone {
		// there's no actual way/need to specify native/wasm execution strategy on light node
		// => we can safely ignore passed values

		match self.backend.is_local_state_available(at) {
			true => CallExecutor::contextual_call::<
				_,
				_,
				fn(
					Result<NativeOrEncoded<R>, Local::Error>,
					Result<NativeOrEncoded<R>, Local::Error>,
				) -> Result<NativeOrEncoded<R>, Local::Error>,
				_,
				NC
			>(
				&self.local,
				initialize_block_fn,
				at,
				method,
				call_data,
				changes,
				initialize_block,
				ExecutionManager::NativeWhenPossible,
				native_call,
				side_effects_handler,
				recorder,
			).map_err(|e| ClientError::Execution(Box::new(e.to_string()))),
			false => CallExecutor::contextual_call::<
				_,
				_,
				fn(
					Result<NativeOrEncoded<R>, Remote::Error>,
					Result<NativeOrEncoded<R>, Remote::Error>,
				) -> Result<NativeOrEncoded<R>, Remote::Error>,
				_,
				NC
			>(
				&self.remote,
				initialize_block_fn,
				at,
				method,
				call_data,
				changes,
				initialize_block,
				ExecutionManager::NativeWhenPossible,
				native_call,
				side_effects_handler,
				recorder,
			).map_err(|e| ClientError::Execution(Box::new(e.to_string()))),
		}
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		match self.backend.is_local_state_available(id) {
			true => self.local.runtime_version(id),
			false => self.remote.runtime_version(id),
		}
	}

	fn call_at_state<
		O: offchain::Externalities,
		S: StateBackend<Blake2Hasher>,
		FF: FnOnce(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
	>(&self,
		state: &S,
		changes: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8],
		_manager: ExecutionManager<FF>,
		native_call: Option<NC>,
		side_effects_handler: Option<&mut O>,
	) -> ClientResult<(NativeOrEncoded<R>, S::Transaction, Option<MemoryDB<Blake2Hasher>>)> {
		// there's no actual way/need to specify native/wasm execution strategy on light node
		// => we can safely ignore passed values

		CallExecutor::call_at_state::<
				_,
				_,
				fn(
					Result<NativeOrEncoded<R>, Remote::Error>,
					Result<NativeOrEncoded<R>, Remote::Error>,
				) -> Result<NativeOrEncoded<R>, Remote::Error>,
				_,
				NC
			>(
				&self.remote,
				state,
				changes,
				method,
				call_data,
				ExecutionManager::NativeWhenPossible,
				native_call,
				side_effects_handler,
			).map_err(|e| ClientError::Execution(Box::new(e.to_string())))
	}

	fn prove_at_trie_state<S: state_machine::TrieBackendStorage<Blake2Hasher>>(
		&self,
		state: &state_machine::TrieBackend<S, Blake2Hasher>,
		changes: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		self.remote.prove_at_trie_state(state, changes, method, call_data)
	}

	fn native_runtime_version(&self) -> Option<&NativeVersion> {
		None
	}
}

/// Prove contextual execution using given block header in environment.
///
/// Method is executed using passed header as environment' current block.
/// Proof includes both environment preparation proof and method execution proof.
pub fn prove_execution<Block, S, E>(
	mut state: S,
	header: Block::Header,
	executor: &E,
	method: &str,
	call_data: &[u8],
) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)>
	where
		Block: BlockT<Hash=H256>,
		S: StateBackend<Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
{
	let trie_state = state.as_trie_backend()
		.ok_or_else(|| Box::new(state_machine::ExecutionError::UnableToGenerateProof) as Box<dyn state_machine::Error>)?;

	// prepare execution environment + record preparation proof
	let mut changes = Default::default();
	let (_, init_proof) = executor.prove_at_trie_state(
		trie_state,
		&mut changes,
		"Core_initialize_block",
		&header.encode(),
	)?;

	// execute method + record execution proof
	let (result, exec_proof) = executor.prove_at_trie_state(&trie_state, &mut changes, method, call_data)?;
	let total_proof = init_proof.into_iter()
		.chain(exec_proof.into_iter())
		.collect::<HashSet<_>>()
		.into_iter()
		.collect();

	Ok((result, total_proof))
}

/// Check remote contextual execution proof using given backend.
///
/// Method is executed using passed header as environment' current block.
/// Proof should include both environment preparation proof and method execution proof.
pub fn check_execution_proof<Header, E, H>(
	executor: &E,
	request: &RemoteCallRequest<Header>,
	remote_proof: Vec<Vec<u8>>
) -> ClientResult<Vec<u8>>
	where
		Header: HeaderT,
		E: CodeExecutor<H>,
		H: Hasher,
		H::Out: Ord + 'static,
{
	let local_state_root = request.header.state_root();
	let root: H::Out = convert_hash(&local_state_root);

	// prepare execution environment + check preparation proof
	let mut changes = OverlayedChanges::default();
	let trie_backend = create_proof_check_backend(root, remote_proof)?;
	let next_block = <Header as HeaderT>::new(
		*request.header.number() + One::one(),
		Default::default(),
		Default::default(),
		request.header.hash(),
		request.header.digest().clone(),
	);
	execution_proof_check_on_trie_backend::<H, _>(
		&trie_backend,
		&mut changes,
		executor,
		"Core_initialize_block",
		&next_block.encode(),
	)?;

	// execute method
	let local_result = execution_proof_check_on_trie_backend::<H, _>(
		&trie_backend,
		&mut changes,
		executor,
		&request.method,
		&request.call_data,
	)?;

	Ok(local_result)
}

#[cfg(test)]
mod tests {
	use consensus::BlockOrigin;
	use test_client::{self, runtime::{Block, Header}, runtime::RuntimeApi, TestClient};
	use executor::NativeExecutionDispatch;
	use crate::backend::{Backend, NewBlockState};
	use crate::in_mem::Backend as InMemBackend;
	use crate::light::fetcher::tests::OkCallFetcher;
	use super::*;

	#[test]
	fn execution_proof_is_generated_and_checked() {
		type TestClient = test_client::client::Client<
			test_client::Backend,
			test_client::Executor,
			Block,
			RuntimeApi
		>;

		fn execute(remote_client: &TestClient, at: u64, method: &'static str) -> (Vec<u8>, Vec<u8>) {
			let remote_block_id = BlockId::Number(at);
			let remote_root = remote_client.state_at(&remote_block_id)
				.unwrap().storage_root(::std::iter::empty()).0;

			// 'fetch' execution proof from remote node
			let (remote_result, remote_execution_proof) = remote_client.execution_proof(
				&remote_block_id,
				method,
				&[]
			).unwrap();

			// check remote execution proof locally
			let local_executor = test_client::LocalExecutor::new(None);
			let local_result = check_execution_proof(&local_executor, &RemoteCallRequest {
				block: test_client::runtime::Hash::default(),
				header: test_client::runtime::Header {
					state_root: remote_root.into(),
					parent_hash: Default::default(),
					number: at,
					extrinsics_root: Default::default(),
					digest: Default::default(),
				},
				method: method.into(),
				call_data: vec![],
				retry_count: None,
			}, remote_execution_proof).unwrap();

			(remote_result, local_result)
		}

		// prepare remote client
		let remote_client = test_client::new();
		for _ in 1..3 {
			remote_client.import_justified(
				BlockOrigin::Own,
				remote_client.new_block(Default::default()).unwrap().bake().unwrap(),
				Default::default(),
			).unwrap();
		}

		// check method that doesn't requires environment
		let (remote, local) = execute(&remote_client, 0, "Core_version");
		assert_eq!(remote, local);

		// check method that requires environment
		let (_, block) = execute(&remote_client, 0, "BlockBuilder_finalize_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 1);

		// check method that requires environment
		let (_, block) = execute(&remote_client, 2, "BlockBuilder_finalize_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 3);
	}

	#[test]
	fn code_is_executed_locally_or_remotely() {
		let backend = Arc::new(InMemBackend::new());
		let def = H256::default();
		let header0 = test_client::runtime::Header::new(0, def, def, def, Default::default());
		let hash0 = header0.hash();
		let header1 = test_client::runtime::Header::new(1, def, def, hash0, Default::default());
		let hash1 = header1.hash();
		backend.blockchain().insert(hash0, header0, None, None, NewBlockState::Final).unwrap();
		backend.blockchain().insert(hash1, header1, None, None, NewBlockState::Final).unwrap();

		let local_executor = RemoteCallExecutor::new(Arc::new(backend.blockchain().clone()), Arc::new(OkCallFetcher::new(vec![1])));
		let remote_executor = RemoteCallExecutor::new(Arc::new(backend.blockchain().clone()), Arc::new(OkCallFetcher::new(vec![2])));
		let remote_or_local = RemoteOrLocalCallExecutor::new(backend, remote_executor, local_executor);
		assert_eq!(remote_or_local.call(&BlockId::Number(0), "test_method", &[], ExecutionStrategy::NativeElseWasm, NeverOffchainExt::new()).unwrap(), vec![1]);
		assert_eq!(remote_or_local.call(&BlockId::Number(1), "test_method", &[], ExecutionStrategy::NativeElseWasm, NeverOffchainExt::new()).unwrap(), vec![2]);
	}
}
