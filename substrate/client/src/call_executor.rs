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

use std::sync::Arc;
use futures::{IntoFuture, Future};
use primitives::Hash;
use primitives::block::{Id as BlockId, HeaderHash};
use state_machine::{self, OverlayedChanges, Backend as StateBackend, CodeExecutor};

use backend;
use blockchain::Backend as ChainBackend;
use error;
use light::{Fetcher, RemoteCallRequest};

/// Information regarding the result of a call.
#[derive(Debug, Clone)]
pub struct CallResult {
	/// The data that was returned from the call.
	pub return_data: Vec<u8>,
	/// The changes made to the state by the call.
	pub changes: OverlayedChanges,
}

/// Method call executor.
pub trait CallExecutor {
	/// Externalities error type.
	type Error: state_machine::Error;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> Result<CallResult, error::Error>;

	/// Execute a call to a contract on top of given state.
	///
	/// No changes are made.
	fn call_at_state<S: state_machine::Backend>(&self, state: &S, overlay: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, S::Transaction), error::Error>;

	/// Execute a call to a contract on top of given state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_state<S: state_machine::Backend>(&self, state: S, overlay: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error>;
}

/// Method call execution cache.
///
/// It only makes sense to use this cache to cache readonly calls, since it only caches
/// CallResult::return_data (CallResult::changes are 'cached' empty).
pub trait CallExecutorCache {
	/// Cache call result.
	fn cache_call(&self, block: &HeaderHash, method: &str, call_data: &[u8], return_data: &[u8]);

	/// Try to get call result from the cache.
	fn cached_call(&self, block: &HeaderHash, method: &str, call_data: &[u8]) -> Option<Vec<u8>>;
}

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
}

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F, C> {
	blockchain: Arc<B>,
	fetcher: Arc<F>,
	cache: C,
}

impl<B, E> LocalCallExecutor<B, E> {
	/// Creates new instance of local call executor.
	pub fn new(backend: Arc<B>, executor: E) -> Self {
		LocalCallExecutor { backend, executor }
	}
}

impl<B, E> Clone for LocalCallExecutor<B, E> where E: Clone {
	fn clone(&self) -> Self {
		LocalCallExecutor {
			backend: self.backend.clone(),
			executor: self.executor.clone(),
		}
	}
}

impl<B, E> CallExecutor for LocalCallExecutor<B, E>
	where
		B: backend::LocalBackend,
		E: CodeExecutor,
		error::Error: From<<<B as backend::Backend>::State as StateBackend>::Error>,
{
	type Error = E::Error;

	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let mut changes = OverlayedChanges::default();
		let (return_data, _) = self.call_at_state(&self.backend.state_at(*id)?, &mut changes, method, call_data)?;
		Ok(CallResult{ return_data, changes })
	}

	fn call_at_state<S: state_machine::Backend>(&self, state: &S, changes: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, S::Transaction)> {
		state_machine::execute(
			state,
			changes,
			&self.executor,
			method,
			call_data,
		).map_err(Into::into)
	}

	fn prove_at_state<S: state_machine::Backend>(&self, state: S, changes: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error> {
		state_machine::prove_execution(
			state,
			changes,
			&self.executor,
			method,
			call_data,
		)
		.map(|(result, proof, _)| (result, proof))
		.map_err(Into::into)
	}
}

impl<B, F, C> RemoteCallExecutor<B, F, C> {
	/// Creates new instance of remote call executor.
	pub fn new(blockchain: Arc<B>, fetcher: Arc<F>, cache: C) -> Self {
		RemoteCallExecutor { blockchain, fetcher, cache }
	}
}

impl<B, F, C> CallExecutor for RemoteCallExecutor<B, F, C>
	where
		B: ChainBackend,
		F: Fetcher,
		C: CallExecutorCache,
{
	type Error = error::Error;

	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.blockchain.hash(number)?
				.ok_or_else(|| error::ErrorKind::UnknownBlock(BlockId::Number(number)))?,
		};

		// try to read from cache
		if let Some(cached_result) = self.cache.cached_call(&block_hash, method, call_data) {
			return Ok(CallResult {
				return_data: cached_result,
				changes: Default::default(),
			});
		}

		// fetch and check execution proof from remote node
		let call_result = self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash.clone(),
			method: method.into(),
			call_data: call_data.to_vec(),
			..Default::default()
		}).into_future().wait()?;

		// only cache results when changes are empty
		if call_result.changes.is_empty() {
			self.cache.cache_call(&block_hash, method, call_data, &call_result.return_data);
		}

		Ok(call_result)
	}

	fn call_at_state<S: state_machine::Backend>(&self, _state: &S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> error::Result<(Vec<u8>, S::Transaction)> {
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
	}

	fn prove_at_state<S: state_machine::Backend>(&self, _state: S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error> {
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
	}
}

/// Check remote execution proof using given backend.
pub fn check_execution_proof<B, E>(blockchain: &B, executor: &E, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> Result<CallResult, error::Error>
	where
		B: ChainBackend,
		E: CodeExecutor,
{
	let local_header = blockchain.header(BlockId::Hash(request.block))?;
	let local_header = local_header.ok_or_else(|| error::ErrorKind::UnknownBlock(BlockId::Hash(request.block)))?;
	let local_state_root = local_header.state_root;
	do_check_execution_proof(local_state_root, executor, request, remote_proof)
}

/// Check remote execution proof using given state root.
fn do_check_execution_proof<E>(local_state_root: Hash, executor: &E, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> Result<CallResult, error::Error>
	where
		E: CodeExecutor,
{
	let (remote_result, remote_proof) = remote_proof;

	let mut changes = OverlayedChanges::default();
	let (local_result, _) = state_machine::execution_proof_check(
		local_state_root.into(),
		remote_proof,
		&mut changes,
		executor,
		&request.method,
		&request.call_data)?;

	if local_result != remote_result {
		return Err(error::ErrorKind::InvalidExecutionProof.into());
	}

	Ok(CallResult { return_data: local_result, changes })
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use std::sync::Arc;
	use parking_lot::Mutex;
	use primitives::block::{Id as BlockId, HeaderHash};
	use state_machine::Backend;
	use test_client;
	use in_mem::{Backend as InMemoryBackend};
	use light::{RemoteCallRequest, Blockchain, new_light_blockchain};
	use light::tests::OkCallFetcher;
	use super::{do_check_execution_proof, CallExecutor, CallExecutorCache,
		RemoteCallExecutor, CallResult};

	#[derive(Default)]
	struct InMemoryCallCache {
		data: Mutex<InMemoryCallCacheData>,
	}

	#[derive(Default)]
	struct InMemoryCallCacheData {
		cache_accesses: usize,
		cache_matches: usize,
		cache: HashMap<(HeaderHash, String, Vec<u8>), Vec<u8>>,
	}

	impl CallExecutorCache for InMemoryCallCache {
		fn cache_call(&self, block: &HeaderHash, method: &str, call_data: &[u8], return_data: &[u8]) {
			self.data.lock().cache.insert((block.clone(), method.into(), call_data.to_vec()), return_data.to_vec());
		}

		fn cached_call(&self, block: &HeaderHash, method: &str, call_data: &[u8]) -> Option<Vec<u8>> {
			let mut data = self.data.lock();
			data.cache_accesses += 1;
			match data.cache.get(&(block.clone(), method.into(), call_data.to_vec())).cloned() {
				Some(result) => {
					data.cache_matches += 1;
					Some(result)
				},
				None => None,
			}
		}
	}

	#[test]
	fn execution_proof_is_generated_and_checked() {
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_storage_root = remote_client.state_at(&remote_block_id)
			.unwrap().storage_root(::std::iter::empty()).0;

		// 'fetch' execution proof from remote node
		let remote_execution_proof = remote_client.execution_proof(&remote_block_id, "authorities", &[]).unwrap();

		// check remote execution proof locally
		let local_executor = test_client::NativeExecutor::new();
		do_check_execution_proof(remote_block_storage_root.into(), &local_executor, &RemoteCallRequest {
			block: Default::default(),
			method: "authorities".into(),
			call_data: vec![],
			..Default::default()
		}, remote_execution_proof).unwrap();
	}

	#[test]
	fn execution_proof_is_cached() {
		let fetcher = OkCallFetcher::new(CallResult {
			return_data: vec![42],
			changes: Default::default(),
		});
		let light_blockchain: Arc<Blockchain<InMemoryBackend, OkCallFetcher>> = new_light_blockchain(InMemoryBackend::new());

		// cache is empty initially
		let call_executor = RemoteCallExecutor::new(light_blockchain, Arc::new(fetcher), InMemoryCallCache::default());
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 0);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 0);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 0);

		// cache entry is created after successful call
		call_executor.call(&BlockId::Hash(Default::default()), "test", &[]).unwrap();
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 1);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 0);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 1);

		// cache entry is used when called with same arguments
		call_executor.call(&BlockId::Hash(Default::default()), "test", &[]).unwrap();
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 2);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 1);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 1);

		// cache entry is NOT used when called with same arguments
		// new cache entry is crated when called with other arguments
		call_executor.call(&BlockId::Hash(Default::default()), "test", &[1]).unwrap();
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 3);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 1);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 2);

		// cache entry is NOT used when called at other block
		// new cache entry is crated when called at other block
		call_executor.call(&BlockId::Hash(1.into()), "test", &[]).unwrap();
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 4);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 1);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 3);

		// cache entry is NOT used when calling other method
		// new cache entry is crated when calling other method
		call_executor.call(&BlockId::Hash(Default::default()), "test1", &[]).unwrap();
		assert_eq!(call_executor.cache.data.lock().cache_accesses, 5);
		assert_eq!(call_executor.cache.data.lock().cache_matches, 1);
		assert_eq!(call_executor.cache.data.lock().cache.len(), 4);
	}
}
