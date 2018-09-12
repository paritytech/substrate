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

//! Light client call exector. Executes methods on remote full nodes, fetching
//! execution proof and checking it locally.

use std::marker::PhantomData;
use std::sync::Arc;
use futures::{IntoFuture, Future};

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use state_machine::{Backend as StateBackend, CodeExecutor, OverlayedChanges,
	execution_proof_check, ExecutionManager};
use primitives::H256;
use patricia_trie::NodeCodec;
use hashdb::Hasher;
use rlp::Encodable;

use blockchain::Backend as ChainBackend;
use call_executor::{CallExecutor, CallResult};
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::fetcher::{Fetcher, RemoteCallRequest};
use executor::RuntimeVersion;
use codec::Decode;
use heapsize::HeapSizeOf;
use memorydb::MemoryDB;

/// Call executor that executes methods on remote node, querying execution proof
/// and checking proof by re-executing locally.
pub struct RemoteCallExecutor<B, F, H, C> {
	blockchain: Arc<B>,
	fetcher: Arc<F>,
	_hasher: PhantomData<H>,
	_codec: PhantomData<C>,
}

impl<B, F, H, C> Clone for RemoteCallExecutor<B, F, H, C> {
	fn clone(&self) -> Self {
		RemoteCallExecutor {
			blockchain: self.blockchain.clone(),
			fetcher: self.fetcher.clone(),
			_hasher: Default::default(),
			_codec: Default::default(),
		}
	}
}

impl<B, F, H, C> RemoteCallExecutor<B, F, H, C> {
	/// Creates new instance of remote call executor.
	pub fn new(blockchain: Arc<B>, fetcher: Arc<F>) -> Self {
		RemoteCallExecutor { blockchain, fetcher, _hasher: PhantomData, _codec: PhantomData }
	}
}

impl<B, F, Block, H, C> CallExecutor<Block, H, C> for RemoteCallExecutor<B, F, H, C>
where
	Block: BlockT,
	B: ChainBackend<Block>,
	F: Fetcher<Block>,
	H: Hasher,
	H::Out: Ord + Encodable,
	C: NodeCodec<H>
{
	type Error = ClientError;

	fn call(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> ClientResult<CallResult> {
		let block_hash = match *id {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.blockchain.hash(number)?
				.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", number)))?,
		};
		let block_header = self.blockchain.expect_header(id.clone())?;

		self.fetcher.remote_call(RemoteCallRequest {
			block: block_hash,
			header: block_header,
			method: method.into(),
			call_data: call_data.to_vec(),
			retry_count: None,
		}).into_future().wait()
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		let call_result = self.call(id, "version", &[])?;
		RuntimeVersion::decode(&mut call_result.return_data.as_slice())
			.ok_or_else(|| ClientErrorKind::VersionInvalid.into())
	}

	fn call_at_state<
		S: StateBackend<H, C>,
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

	fn prove_at_state<S: StateBackend<H, C>>(
		&self,
		_state: S,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8]
	) -> ClientResult<(Vec<u8>, Vec<Vec<u8>>)> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into())
	}

	fn native_runtime_version(&self) -> Option<RuntimeVersion> {
		None
	}
}

/// Check remote execution proof using given backend.
pub fn check_execution_proof<Header, E, H, C>(
	executor: &E,
	request: &RemoteCallRequest<Header>,
	remote_proof: Vec<Vec<u8>>
) -> ClientResult<CallResult>
	where
		Header: HeaderT,
		E: CodeExecutor<H>,
		H: Hasher,
		H::Out: Ord + Encodable + HeapSizeOf + From<H256>,
		C: NodeCodec<H>,
{
	let local_state_root = request.header.state_root();

	let mut changes = OverlayedChanges::default();
	let local_result = execution_proof_check::<H, C, _>(
		H256::from_slice(local_state_root.as_ref()).into(),
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
	use primitives::RlpCodec;

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
		let local_executor = test_client::LocalExecutor::new();
		check_execution_proof::<_, _, _, RlpCodec>(&local_executor, &RemoteCallRequest {
			block: test_client::runtime::Hash::default(),
			header: test_client::runtime::Header {
				state_root: remote_block_storage_root.into(),
				parent_hash: Default::default(),
				number: 0,
				extrinsics_root: Default::default(),
				digest: Default::default(),
			},
			method: "authorities".into(),
			call_data: vec![],
			retry_count: None,
		}, remote_execution_proof).unwrap();
	}
}
