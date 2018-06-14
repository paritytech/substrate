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

//! Light client data fetcher. Fetches requested data from remote full nodes.

use std::sync::Arc;
use futures::IntoFuture;
use heapsize::HeapSizeOf;

use primitives::block::{HeaderHash, Id as BlockId};
use state_machine::{CodeExecutor, read_proof_check};

use backend::Backend as ClientBackend;
use blockchain::Backend as BlockchainBackend;
use call_executor::CallResult;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::Blockchain;
use light::call_executor::check_execution_proof;

/// Remote storage read request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteReadRequest {
	/// Read at state of given block.
	pub block: HeaderHash,
	/// Storage key to read.
	pub key: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Remote call request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest {
	/// Call at state of given block.
	pub block: HeaderHash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher: Send + Sync {
	/// Remote storage read future.
	type RemoteReadResult: IntoFuture<Item=Option<Vec<u8>>, Error=ClientError>;
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=ClientError>;

	/// Fetch remote storage value.
	fn remote_read(&self, request: RemoteReadRequest) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker: Send + Sync {
	/// Check remote storage read proof.
	fn check_read_proof(&self, request: &RemoteReadRequest, remote_proot: Vec<Vec<u8>>) -> ClientResult<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> ClientResult<CallResult>;
}

/// Remote data checker.
pub struct LightDataChecker<B, E, F> {
	blockchain: Arc<Blockchain<B, F>>,
	executor: E,
}

impl<B, E, F> LightDataChecker<B, E, F> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<B, F>>, executor: E) -> Self {
		Self {
			blockchain,
			executor,
		}
	}

	/// Get blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<B, F>> {
		&self.blockchain
	}
}

impl<B, E, F> FetchChecker for LightDataChecker<B, E, F>
	where
		B: ClientBackend,
		E: CodeExecutor,
		F: Fetcher,
{
	fn check_read_proof(&self, request: &RemoteReadRequest, remote_proof: Vec<Vec<u8>>) -> ClientResult<Option<Vec<u8>>> {
		let local_header = self.blockchain.header(BlockId::Hash(request.block))?;
		let local_header = local_header.ok_or_else(|| ClientErrorKind::UnknownBlock(BlockId::Hash(request.block)))?;
		let local_state_root = local_header.state_root;
		read_proof_check(local_state_root.0, remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> ClientResult<CallResult> {
		check_execution_proof(&*self.blockchain, &self.executor, request, remote_proof)
	}
}

impl HeapSizeOf for RemoteReadRequest {
	fn heap_size_of_children(&self) -> usize {
		self.block.heap_size_of_children() + self.key.heap_size_of_children()
	}
}

impl HeapSizeOf for RemoteCallRequest {
	fn heap_size_of_children(&self) -> usize {
		self.block.heap_size_of_children() + self.method.heap_size_of_children()
			+ self.call_data.heap_size_of_children()
	}
}
