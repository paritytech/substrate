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

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT};
use state_machine::{CodeExecutor, read_proof_check};

use blockchain::HeaderBackend as BlockchainHeaderBackend;
use cht;
use call_executor::CallResult;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::call_executor::check_execution_proof;

/// Remote canonical header request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteHeaderRequest<Number: ::std::fmt::Display> {
	/// Number of the header to query.
	pub block: Number,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Remote storage read request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteReadRequest<Hash: ::std::fmt::Display> {
	/// Read at state of given block.
	pub block: Hash,
	/// Storage key to read.
	pub key: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Remote call request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest<Hash: ::std::fmt::Display> {
	/// Call at state of given block.
	pub block: Hash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher<Block: BlockT>: Send + Sync {
	/// Remote header future.
	type RemoteHeaderResult: IntoFuture<Item=Block::Header, Error=ClientError>;
	/// Remote storage read future.
	type RemoteReadResult: IntoFuture<Item=Option<Vec<u8>>, Error=ClientError>;
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=ClientError>;

	/// Fetch remote header.
	fn remote_header(&self, request: RemoteHeaderRequest<<<Block as BlockT>::Header as HeaderT>::Number>) -> Self::RemoteHeaderResult;
	/// Fetch remote storage value.
	fn remote_read(&self, request: RemoteReadRequest<Block::Hash>) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<Block::Hash>) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker<Block: BlockT>: Send + Sync {
	/// Check remote header proof.
	fn check_header_proof(&self, request: &RemoteHeaderRequest<<<Block as BlockT>::Header as HeaderT>::Number>, header: Block::Header, remote_proof: Vec<Vec<u8>>) -> ClientResult<Block::Header>;
	/// Check remote storage read proof.
	fn check_read_proof(&self, request: &RemoteReadRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult>;
}

/// Remote data checker.
pub struct LightDataChecker<S, E, F> {
	blockchain: Arc<Blockchain<S, F>>,
	executor: E,
}

impl<S, E, F> LightDataChecker<S, E, F> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<S, F>>, executor: E) -> Self {
		Self {
			blockchain,
			executor,
		}
	}

	/// Get blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}
}

impl<S, E, F, Block> FetchChecker<Block> for LightDataChecker<S, E, F>
	where
		Block: BlockT,
		<Block as BlockT>::Hash: From<[u8; 32]> + Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
		<<Block as BlockT>::Header as HeaderT>::Number: As<u32>,
		S: BlockchainStorage<Block>,
		E: CodeExecutor,
		F: Fetcher<Block>,
{
	fn check_header_proof(&self, request: &RemoteHeaderRequest<<<Block as BlockT>::Header as HeaderT>::Number>, header: Block::Header, remote_proof: Vec<Vec<u8>>) -> ClientResult<Block::Header> {
		let local_cht_root = self.blockchain.storage().cht_root(request.block)?;
		let remote_hash = header.hash();
		cht::check_proof::<Block::Header>(local_cht_root, request.block, remote_hash, remote_proof)
			.map(|_| header)
	}

	fn check_read_proof(&self, request: &RemoteReadRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<Option<Vec<u8>>> {
		let local_header = self.blockchain.header(BlockId::Hash(request.block))?;
		let local_header = local_header.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", request.block)))?;
		let local_state_root = *local_header.state_root();
		read_proof_check(local_state_root.into(), remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(&self, request: &RemoteCallRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult> {
		check_execution_proof(&*self.blockchain, &self.executor, request, remote_proof)
	}
}

impl<Number: ::std::fmt::Display> HeapSizeOf for RemoteHeaderRequest<Number> {
	fn heap_size_of_children(&self) -> usize {
		0
	}
}

impl<Hash: ::std::fmt::Display> HeapSizeOf for RemoteReadRequest<Hash> {
	fn heap_size_of_children(&self) -> usize {
		// TODO: self.block.heap_size_of_children() +
		self.key.heap_size_of_children()
	}
}

impl<Hash: ::std::fmt::Display> HeapSizeOf for RemoteCallRequest<Hash> {
	fn heap_size_of_children(&self) -> usize {
		// TODO: self.block.heap_size_of_children() +
		self.method.heap_size_of_children()
			+ self.call_data.heap_size_of_children()
	}
}
