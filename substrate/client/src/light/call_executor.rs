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

//! Light client call exector. Executes methods on remote full nodes, fetching
//! execution proof and checking it locally.

use std::sync::Arc;
use futures::{IntoFuture, Future};
use heapsize::HeapSizeOf;

use primitives::Hash;
use primitives::block::Id as BlockId;
use state_machine::{Backend as StateBackend, CodeExecutor, OverlayedChanges, execution_proof_check};

use blockchain::Backend as ChainBackend;
use call_executor::{CallExecutor, CallResult};
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::fetcher::{Fetcher, RemoteCallRequest};

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F> {
	blockchain: Arc<B>,
	fetcher: Arc<F>,
}

impl<B, F> RemoteCallExecutor<B, F> {
	/// Creates new instance of remote call executor.
	pub fn new(blockchain: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { blockchain, fetcher }
	}
}

impl<B, F> CallExecutor for RemoteCallExecutor<B, F>
	where
		B: ChainBackend,
		F: Fetcher,
{
	type Error = ClientError;

	fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> ClientResult<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.blockchain.hash(number)?
				.ok_or_else(|| ClientErrorKind::UnknownBlock(BlockId::Number(number)))?,
		};

		self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash.clone(),
			method: method.into(),
			call_data: call_data.to_vec(),
			..Default::default()
		}).into_future().wait()
	}

	fn call_at_state<S: StateBackend>(&self, _state: &S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> ClientResult<(Vec<u8>, S::Transaction)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn prove_at_state<S: StateBackend>(&self, _state: S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}
}

/// Check remote execution proof using given backend.
pub fn check_execution_proof<B, E>(blockchain: &B, executor: &E, request: &RemoteCallRequest, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult>
	where
		B: ChainBackend,
		E: CodeExecutor,
{
	let local_header = blockchain.header(BlockId::Hash(request.block))?;
	let local_header = local_header.ok_or_else(|| ClientErrorKind::UnknownBlock(BlockId::Hash(request.block)))?;
	let local_state_root = local_header.state_root;
	do_check_execution_proof(local_state_root, executor, request, remote_proof)
}

/// Check remote execution proof using given state root.
fn do_check_execution_proof<E>(local_state_root: Hash, executor: &E, request: &RemoteCallRequest, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult>
	where
		E: CodeExecutor,
{
	let mut changes = OverlayedChanges::default();
	let (local_result, _) = execution_proof_check(
		local_state_root.into(),
		remote_proof,
		&mut changes,
		executor,
		&request.method,
		&request.call_data)?;

	Ok(CallResult { return_data: local_result, changes })
}

impl HeapSizeOf for CallResult {
	fn heap_size_of_children(&self) -> usize {
		self.return_data.heap_size_of_children() + self.changes.heap_size_of_children()
	}
}

#[cfg(test)]
mod tests {
	use primitives::block::Id as BlockId;
	use state_machine::Backend;
	use test_client;
	use light::fetcher::RemoteCallRequest;
	use super::do_check_execution_proof;

	#[test]
	fn execution_proof_is_generated_and_checked() {
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_storage_root = remote_client.state_at(&remote_block_id)
			.unwrap().storage_root(::std::iter::empty()).0;

		// 'fetch' execution proof from remote node
		let remote_execution_proof = remote_client.execution_proof(&remote_block_id, "authorities", &[]).unwrap().1;

		// check remote execution proof locally
		let local_executor = test_client::NativeExecutor::new();
		do_check_execution_proof(remote_block_storage_root.into(), &local_executor, &RemoteCallRequest {
			block: Default::default(),
			method: "authorities".into(),
			call_data: vec![],
			..Default::default()
		}, remote_execution_proof).unwrap();
	}
}
