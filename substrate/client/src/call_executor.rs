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
use primitives::block::Id as BlockId;
use state_machine::{self, OverlayedChanges, Backend as StateBackend, CodeExecutor};

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
		state_machine::prove(
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

impl<B, F> RemoteCallExecutor<B, F> {
	/// Creates new instance of remote call executor.
	pub fn new(backend: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { backend, fetcher }
	}
}

impl<B, F> CallExecutor for RemoteCallExecutor<B, F>
	where
		B: backend::RemoteBackend,
		F: Fetcher,
		error::Error: From<<<B as backend::Backend>::State as StateBackend>::Error>,
{
	type Error = error::Error;

	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.backend.blockchain().hash(number)?
				.ok_or_else(|| error::ErrorKind::UnknownBlock(BlockId::Number(number)))?,
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

	fn prove_at_state<S: state_machine::Backend>(&self, _state: S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error> {
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
	}
}

/// Check remote execution proof using given backend.
pub fn check_execution_proof<B, E>(backend: &B, executor: &E, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> Result<CallResult, error::Error>
	where
		B: backend::RemoteBackend,
		E: CodeExecutor,
		error::Error: From<<<B as backend::Backend>::State as StateBackend>::Error>,
{
	let local_header = backend.blockchain().header(BlockId::Hash(request.block))?;
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
	let (local_result, _) = state_machine::proof_check(
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
	use primitives::block::Id as BlockId;
	use state_machine::Backend;
	use test_client;
	use light::RemoteCallRequest;
	use super::do_check_execution_proof;

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
		}, remote_execution_proof).unwrap();
	}
}
