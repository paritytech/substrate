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

use hash_db::Hasher;
use heapsize::HeapSizeOf;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use state_machine::{CodeExecutor, read_proof_check};
use std::marker::PhantomData;

use call_executor::CallResult;
use cht;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
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
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
}

/// Remote canonical header request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteHeaderRequest<Header: HeaderT> {
	/// The root of CHT this block is included in.
	pub cht_root: Header::Hash,
	/// Number of the header to query.
	pub block: Header::Number,
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
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
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
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
	fn remote_header(&self, request: RemoteHeaderRequest<Block::Header>) -> Self::RemoteHeaderResult;
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
	/// Check remote header proof.
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<Block::Header>,
		header: Option<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Block::Header>;
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
pub struct LightDataChecker<E, H> {
	executor: E,
	_hasher: PhantomData<H>,
}

impl<E, H> LightDataChecker<E, H> {
	/// Create new light data checker.
	pub fn new(executor: E) -> Self {
		Self {
			executor, _hasher: PhantomData
		}
	}
}

impl<E, Block, H> FetchChecker<Block> for LightDataChecker<E, H>
	where
		Block: BlockT,
		E: CodeExecutor<H>,
		H: Hasher,
		H::Out: Ord + HeapSizeOf,
{
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<Block::Header>,
		remote_header: Option<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Block::Header> {
		let remote_header = remote_header.ok_or_else(||
			ClientError::from(ClientErrorKind::InvalidHeaderProof))?;
		let remote_header_hash = remote_header.hash();
		cht::check_proof::<Block::Header, H>(
			request.cht_root,
			request.block,
			remote_header_hash,
			remote_proof)
			.map(|_| remote_header)
	}

	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>> {
		let mut root: H::Out = Default::default();
		root.as_mut().copy_from_slice(request.header.state_root().as_ref());
		read_proof_check::<H>(root, remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<CallResult> {
		check_execution_proof::<_, _, H>(&self.executor, request, remote_proof)
	}
}

#[cfg(test)]
pub mod tests {
	use futures::future::{ok, err, FutureResult};
	use parking_lot::Mutex;
	use call_executor::CallResult;
	use executor::{self, NativeExecutionDispatch};
	use error::Error as ClientError;
	use test_client::{self, TestClient, runtime::{Hash, Block, Header}};
	use test_client::client::BlockOrigin;
	use in_mem::{Blockchain as InMemoryBlockchain};
	use light::fetcher::{Fetcher, FetchChecker, LightDataChecker,
		RemoteCallRequest, RemoteHeaderRequest};
	use primitives::{Blake2Hasher};
	use primitives::storage::well_known_keys;
	use runtime_primitives::generic::BlockId;
	use state_machine::Backend;
	use super::*;

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteHeaderResult = FutureResult<Header, ClientError>;
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_header(&self, _request: RemoteHeaderRequest<Header>) -> Self::RemoteHeaderResult {
			err("Not implemented on test node".into())
		}

		fn remote_read(&self, _request: RemoteReadRequest<Header>) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest<Header>) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}
	}

	fn prepare_for_read_proof_check() -> (
		LightDataChecker<executor::NativeExecutor<test_client::LocalExecutor>, Blake2Hasher>,
		Header, Vec<Vec<u8>>, usize)
	{
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.authorities_at(&remote_block_id).unwrap().len();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, well_known_keys::AUTHORITY_COUNT).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		local_storage.insert(
			remote_block_hash,
			remote_block_header.clone(),
			None,
			None,
			::backend::NewBlockState::Final,
		);
		let local_executor = test_client::LocalExecutor::new();
		let local_checker = LightDataChecker::new(local_executor);
		(local_checker, remote_block_header, remote_read_proof, authorities_len)
	}

	fn prepare_for_header_proof_check(insert_cht: bool) -> (
		LightDataChecker<executor::NativeExecutor<test_client::LocalExecutor>, Blake2Hasher>,
		Hash, Header, Vec<Vec<u8>>)
	{
		// prepare remote client
		let remote_client = test_client::new();
		let mut local_headers_hashes = Vec::new();
		for i in 0..4 {
			let builder = remote_client.new_block().unwrap();
			remote_client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
			local_headers_hashes.push(remote_client.block_hash(i + 1).unwrap());
		}

		// 'fetch' header proof from remote node
		let remote_block_id = BlockId::Number(1);
		let (remote_block_header, remote_header_proof) = remote_client.header_proof_with_cht_size(&remote_block_id, 4).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		let local_cht_root = cht::compute_root::<Header, Blake2Hasher, _>(4, 0, local_headers_hashes.into_iter()).unwrap();
		if insert_cht {
			local_storage.insert_cht_root(1, local_cht_root);
		}
		let local_executor = test_client::LocalExecutor::new();
		let local_checker = LightDataChecker::new(local_executor);
		(local_checker, local_cht_root, remote_block_header, remote_header_proof)
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		let (local_checker, remote_block_header, remote_read_proof, authorities_len) = prepare_for_read_proof_check();
		assert_eq!((&local_checker as &FetchChecker<Block>).check_read_proof(&RemoteReadRequest::<Header> {
			block: remote_block_header.hash(),
			header: remote_block_header,
			key: well_known_keys::AUTHORITY_COUNT.to_vec(),
			retry_count: None,
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}

	#[test]
	fn header_proof_is_generated_and_checked() {
		let (local_checker, local_cht_root, remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		assert_eq!((&local_checker as &FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: local_cht_root,
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).unwrap(), remote_block_header);
	}

	#[test]
	fn check_header_proof_fails_if_cht_root_is_invalid() {
		let (local_checker, _, mut remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		remote_block_header.number = 100;
		assert!((&local_checker as &FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}

	#[test]
	fn check_header_proof_fails_if_invalid_header_provided() {
		let (local_checker, local_cht_root, mut remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		remote_block_header.number = 100;
		assert!((&local_checker as &FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: local_cht_root,
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}
}
