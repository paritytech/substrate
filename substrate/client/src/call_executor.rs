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
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::Block as BlockT;
use state_machine::{self, OverlayedChanges, Backend as StateBackend, CodeExecutor};
use state_machine::backend::InMemory as InMemoryStateBackend;

use backend;
use blockchain::Backend as ChainBackend;
use error;
use light::{Fetcher, RemoteCallRequest};

/// Information regarding the result of a call.
#[derive(Debug)]
pub struct CallResult {
	/// The data that was returned from the call.
	pub return_data: Vec<u8>,
	/// The changes made to the state by the call.
	pub changes: OverlayedChanges,
}

/// Method call executor.
pub trait CallExecutor<B: BlockT> {
	/// Externalities error type.
	type Error: state_machine::Error;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(&self, id: &BlockId<B>, method: &str, call_data: &[u8]) -> Result<CallResult, error::Error>;

	/// Execute a call to a contract on top of given state.
	///
	/// No changes are made.
	fn call_at_state<S: state_machine::Backend>(&self, state: &S, overlay: &mut OverlayedChanges, method: &str, call_data: &[u8]) -> Result<(Vec<u8>, S::Transaction), error::Error>;
}

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
}

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F> {
	backend: Arc<B>,
	fetcher: Arc<F>,
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

impl<B, E, Block> CallExecutor<Block> for LocalCallExecutor<B, E>
	where
		B: backend::LocalBackend<Block>,
		E: CodeExecutor,
		Block: BlockT,
		error::Error: From<<<B as backend::Backend<Block>>::State as StateBackend>::Error>,
{
	type Error = E::Error;

	fn call(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
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
}

impl<B, F> RemoteCallExecutor<B, F> {
	/// Creates new instance of remote call executor.
	pub fn new(backend: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { backend, fetcher }
	}
}

impl<B, F, Block> CallExecutor<Block> for RemoteCallExecutor<B, F>
	where
		B: backend::RemoteBackend<Block>,
		F: Fetcher<Block>,
		Block: BlockT,
		error::Error: From<<<B as backend::Backend<Block>>::State as StateBackend>::Error>,
{
	type Error = error::Error;

	fn call(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.backend.blockchain().hash(number)?
				.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", number)))?,
		};

		self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash,
			method: method.into(),
			call_data: call_data.to_vec(),
		}).into_future().wait()
	}

	fn call_at_state<S: state_machine::Backend>(&self, _state: &S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> error::Result<(Vec<u8>, S::Transaction)> {
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
	}
}

/// Check remote execution proof.
pub fn check_execution_proof<B, E, Block>(backend: &B, executor: &E, request: &RemoteCallRequest<Block::Hash>, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> Result<CallResult, error::Error>
	where
		B: backend::RemoteBackend<Block>,
		E: CodeExecutor,
		Block: BlockT,
		error::Error: From<<<B as backend::Backend<Block>>::State as StateBackend>::Error>,
{
	use runtime_primitives::traits::{Header, Hashing, HashingFor};

	let (remote_result, remote_proof) = remote_proof;

	let remote_state = state_from_execution_proof(remote_proof);
	let remote_state_root = HashingFor::<Block>::trie_root(remote_state.pairs().into_iter());

	let local_header = backend.blockchain().header(BlockId::Hash(request.block))?;
	let local_header = local_header.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", request.block)))?;
	let local_state_root = local_header.state_root().clone();

	if remote_state_root != local_state_root {
		return Err(error::ErrorKind::InvalidExecutionProof.into());
	}

	let mut changes = OverlayedChanges::default();
	let (local_result, _) = state_machine::execute(
		&remote_state,
		&mut changes,
		executor,
		&request.method,
		&request.call_data,
	)?;

	if local_result != remote_result {
		return Err(error::ErrorKind::InvalidExecutionProof.into());
	}

	Ok(CallResult { return_data: local_result, changes })
}

/// Convert state to execution proof. Proof is simple the whole state (temporary).
// TODO [light]: this method must be removed after trie-based proofs are landed.
pub fn state_to_execution_proof<B: state_machine::Backend>(state: &B) -> Vec<Vec<u8>> {
	state.pairs().into_iter()
		.flat_map(|(k, v)| ::std::iter::once(k).chain(::std::iter::once(v)))
		.collect()
}

/// Convert execution proof to in-memory state for check. Reverse function for state_to_execution_proof.
// TODO [light]: this method must be removed after trie-based proofs are landed.
fn state_from_execution_proof(proof: Vec<Vec<u8>>) -> InMemoryStateBackend {
	let mut changes = Vec::new();
	let mut proof_iter = proof.into_iter();
	loop {
		let key = proof_iter.next();
		let value = proof_iter.next();
		if let (Some(key), Some(value)) = (key, value) {
			changes.push((key, Some(value)));
		} else {
			break;
		}
	}

	InMemoryStateBackend::default().update(changes)
}
