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

//! Light client data fetcher. Fetches requested data from remote full nodes.

use futures::IntoFuture;

use primitives::H256;
use hashdb::Hasher;
use patricia_trie::NodeCodec;
use rlp::Encodable;
use heapsize::HeapSizeOf;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use state_machine::{CodeExecutor, read_proof_check};
use std::marker::PhantomData;

use call_executor::CallResult;
use error::{Error as ClientError, Result as ClientResult};
use light::call_executor::check_execution_proof;

/// Remote call request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest<Header: HeaderT> {
	/// Call at state of given block.
	pub block: Header::Hash,
	/// Head of block at which call is perormed.
	pub header: Header,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
}

/// Remote storage read request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteReadRequest<Header: HeaderT> {
	/// Read at state of given block.
	pub block: Header::Hash,
	/// Head of block at which read is perormed.
	pub header: Header,
	/// Storage key to read.
	pub key: Vec<u8>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher<Block: BlockT>: Send + Sync {
	/// Remote storage read future.
	type RemoteReadResult: IntoFuture<Item=Option<Vec<u8>>, Error=ClientError>;
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=ClientError>;

	/// Fetch remote storage value.
	fn remote_read(&self, request: RemoteReadRequest<Block::Header>) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<Block::Header>) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
///
/// Implementations of this trait should not use any blockchain data except that is
/// passed to its methods.
pub trait FetchChecker<Block: BlockT>: Send + Sync {
	/// Check remote storage read proof.
	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<CallResult>;
}

/// Remote data checker.
pub struct LightDataChecker<E, H, C> {
	executor: E,
	_hasher: PhantomData<H>,
	_codec: PhantomData<C>,
}

impl<E, H, C> LightDataChecker<E, H, C> {
	/// Create new light data checker.
	pub fn new(executor: E) -> Self {
		Self {
			executor, _hasher: PhantomData, _codec: PhantomData
		}
	}
}

impl<E, Block, H, C> FetchChecker<Block> for LightDataChecker<E, H, C>
	where
		Block: BlockT,
		Block::Hash: Into<H::Out>,
		E: CodeExecutor<H>,
		H: Hasher,
		C: NodeCodec<H> + Sync + Send,
		H::Out: Ord + Encodable + HeapSizeOf + From<H256>,
{
	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>> {
		let local_state_root = request.header.state_root().clone();
		read_proof_check::<H, C>(local_state_root.into(), remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<CallResult> {
		check_execution_proof::<_, _, H, C>(&self.executor, request, remote_proof)
	}
}
