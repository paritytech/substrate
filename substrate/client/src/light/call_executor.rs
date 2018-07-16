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

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use state_machine::{Backend as StateBackend, CodeExecutor, OverlayedChanges,
	execution_proof_check, TrieH256, ExecutionManager};

use blockchain::Backend as ChainBackend;
use call_executor::{CallExecutor, CallResult};
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::fetcher::{Fetcher, RemoteCallRequest};
use executor::RuntimeVersion;
use codec::Decode;

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

impl<B, F, Block> CallExecutor<Block> for RemoteCallExecutor<B, F>
	where
		Block: BlockT,
		B: ChainBackend<Block>,
		F: Fetcher<Block>,
{
	type Error = ClientError;

	fn call(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> ClientResult<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.blockchain.hash(number)?
				.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", number)))?,
		};

		self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash.clone(),
			method: method.into(),
			call_data: call_data.to_vec(),
		}).into_future().wait()
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		let call_result = self.call(id, "version", &[])?;
		RuntimeVersion::decode(&mut call_result.return_data.as_slice())
			.ok_or_else(|| ClientErrorKind::VersionInvalid.into())
	}

	fn call_at_state<
		S: StateBackend,
		H: FnOnce(Result<Vec<u8>, Self::Error>, Result<Vec<u8>, Self::Error>) -> Result<Vec<u8>, Self::Error>
	>(&self,
		_state: &S,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8],
		_m: ExecutionManager<H>
	) -> ClientResult<(Vec<u8>, S::Transaction)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn prove_at_state<S: StateBackend>(&self, _state: S, _changes: &mut OverlayedChanges, _method: &str, _call_data: &[u8]) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn native_runtime_version(&self) -> Option<RuntimeVersion> {
		None
	}
}

/// Check remote execution proof using given backend.
pub fn check_execution_proof<Block, B, E>(
	blockchain: &B,
	executor: &E,
	request: &RemoteCallRequest<Block::Hash>,
	remote_proof: Vec<Vec<u8>>
) -> ClientResult<CallResult>
	where
		Block: BlockT,
		B: ChainBackend<Block>,
		E: CodeExecutor,
{
	let local_header = blockchain.header(BlockId::Hash(request.block))?;
	let local_header = local_header.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", request.block)))?;
	let local_state_root = *local_header.state_root();
	do_check_execution_proof(local_state_root.into(), executor, request, remote_proof)
}

/// Check remote execution proof using given state root.
fn do_check_execution_proof<Hash, E>(
	local_state_root: Hash,
	executor: &E,
	request: &RemoteCallRequest<Hash>,
	remote_proof: Vec<Vec<u8>>,
) -> ClientResult<CallResult>
	where
		Hash: ::std::fmt::Display + ::std::convert::AsRef<[u8]>,
		E: CodeExecutor,
{
	let mut changes = OverlayedChanges::default();
	let (local_result, _) = execution_proof_check(
		TrieH256::from_slice(local_state_root.as_ref()).into(),
		remote_proof,
		&mut changes,
		executor,
		&request.method,
		&request.call_data)?;

	Ok(CallResult { return_data: local_result, changes })
}

#[cfg(test)]
mod tests {
	use test_client;
	use executor::NativeExecutionDispatch;
	use super::*;

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
		let local_executor = test_client::LocalExecutor::with_heap_pages(8);
		do_check_execution_proof(remote_block_storage_root.into(), &local_executor, &RemoteCallRequest {
			block: test_client::runtime::Hash::default(),
			method: "authorities".into(),
			call_data: vec![],
		}, remote_execution_proof).unwrap();
	}
}
