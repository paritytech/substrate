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

//! Light client call exector. Executes methods on remote full nodes, fetching
//! execution proof and checking it locally.

use std::collections::HashSet;
use std::marker::PhantomData;
use std::sync::Arc;
use futures::{IntoFuture, Future};

use codec::{Encode, Decode};
use primitives::{H256, Blake2Hasher, convert_hash};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT};
use state_machine::{self, Backend as StateBackend, CodeExecutor, OverlayedChanges,
	create_proof_check_backend, execution_proof_check_on_trie_backend, ExecutionManager};
use hash_db::Hasher;

use crate::blockchain::Backend as ChainBackend;
use crate::call_executor::CallExecutor;
use crate::error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use crate::light::fetcher::{Fetcher, RemoteCallRequest};
use executor::{RuntimeVersion, NativeVersion};
use heapsize::HeapSizeOf;
use trie::MemoryDB;

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F, H> {
	blockchain: Arc<B>,
	fetcher: Arc<F>,
	_hasher: PhantomData<H>,
}

impl<B, F, H> Clone for RemoteCallExecutor<B, F, H> {
	fn clone(&self) -> Self {
		RemoteCallExecutor {
			blockchain: self.blockchain.clone(),
			fetcher: self.fetcher.clone(),
			_hasher: Default::default(),
		}
	}
}

impl<B, F, H> RemoteCallExecutor<B, F, H> {
	/// Creates new instance of remote call executor.
	pub fn new(blockchain: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { blockchain, fetcher, _hasher: PhantomData }
	}
}

impl<B, F, Block, H> CallExecutor<Block, H> for RemoteCallExecutor<B, F, H>
where
	Block: BlockT,
	B: ChainBackend<Block>,
	F: Fetcher<Block>,
	H: Hasher<Out=Block::Hash>,
	Block::Hash: Ord,
{
	type Error = ClientError;

	fn call(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> ClientResult<Vec<u8>> {
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
		PB: Fn() -> ClientResult<Block::Header>,
		EM: Fn(Result<Vec<u8>, Self::Error>, Result<Vec<u8>, Self::Error>) -> Result<Vec<u8>, Self::Error>,
	>(
		&self,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		changes: &mut OverlayedChanges,
		initialised_block: &mut Option<BlockId<Block>>,
		_prepare_environment_block: PB,
		_manager: ExecutionManager<EM>,
	) -> ClientResult<Vec<u8>> where ExecutionManager<EM>: Clone {
		// it is only possible to execute contextual call if changes are empty
		if !changes.is_empty() || initialised_block.is_some() {
			return Err(ClientErrorKind::NotAvailableOnLightClient.into());
		}

		self.call(at, method, call_data)
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		let call_result = self.call(id, "version", &[])?;
		RuntimeVersion::decode(&mut call_result.as_slice())
			.ok_or_else(|| ClientErrorKind::VersionInvalid.into())
	}

	fn call_at_state<
		S: StateBackend<H>,
		FF: FnOnce(Result<Vec<u8>, Self::Error>, Result<Vec<u8>, Self::Error>) -> Result<Vec<u8>, Self::Error>
	>(&self,
		_state: &S,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8],
		_m: ExecutionManager<FF>
	) -> ClientResult<(Vec<u8>, S::Transaction, Option<MemoryDB<H>>)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn prove_at_trie_state<S: state_machine::TrieBackendStorage<H>>(
		&self,
		_state: &state_machine::TrieBackend<S, H>,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8]
	) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
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
	state: S,
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
	let trie_state = state.try_into_trie_backend()
		.ok_or_else(|| Box::new(state_machine::ExecutionError::UnableToGenerateProof) as Box<state_machine::Error>)?;

	// prepare execution environment + record preparation proof
	let mut changes = Default::default();
	let (_, init_proof) = executor.prove_at_trie_state(
		&trie_state,
		&mut changes,
		"Core_initialise_block",
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
/// Proof shoul include both environment preparation proof and method execution proof.
pub fn check_execution_proof<Header, E, H>(
	executor: &E,
	request: &RemoteCallRequest<Header>,
	remote_proof: Vec<Vec<u8>>
) -> ClientResult<Vec<u8>>
	where
		Header: HeaderT,
		E: CodeExecutor<H>,
		H: Hasher,
		H::Out: Ord + HeapSizeOf,
{
	let local_state_root = request.header.state_root();
	let root: H::Out = convert_hash(&local_state_root);

	// prepare execution environment + check preparation proof
	let mut changes = OverlayedChanges::default();
	let trie_backend = create_proof_check_backend(root, remote_proof)?;
	let next_block = <Header as HeaderT>::new(
		*request.header.number() + As::sa(1),
		Default::default(),
		Default::default(),
		request.header.hash(),
		Default::default(),
	);
	execution_proof_check_on_trie_backend::<H, _>(
		&trie_backend,
		&mut changes,
		executor,
		"Core_initialise_block",
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
			let local_executor = test_client::LocalExecutor::new();
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
				remote_client.new_block().unwrap().bake().unwrap(),
				Default::default(),
			).unwrap();
		}

		// check method that doesn't requires environment
		let (remote, local) = execute(&remote_client, 0, "Core_authorities");
		assert_eq!(remote, local);

		// check method that requires environment
		let (_, block) = execute(&remote_client, 0, "BlockBuilder_finalise_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 1);

		// check method that requires environment
		let (_, block) = execute(&remote_client, 2, "BlockBuilder_finalise_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 3);
	}
}
