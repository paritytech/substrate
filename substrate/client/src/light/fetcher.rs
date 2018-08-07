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

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use state_machine::{CodeExecutor, read_proof_check};

use call_executor::CallResult;
use cht;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::call_executor::check_execution_proof;
use blockchain::HeaderBackend as BlockchainHeaderBackend;

/// Remote call request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest<Hash: ::std::fmt::Display> {
	/// Call at state of given block.
	pub block: Hash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
}

/// Remote canonical header request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteHeaderRequest<Number: ::std::fmt::Display> {
	/// Number of the header to query.
	pub block: Number,
}

/// Remote storage read request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteReadRequest<Hash: ::std::fmt::Display> {
	/// Read at state of given block.
	pub block: Hash,
	/// Storage key to read.
	pub key: Vec<u8>,
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
	fn remote_header(&self, request: RemoteHeaderRequest<NumberFor<Block>>) -> Self::RemoteHeaderResult;
	/// Fetch remote storage value.
	fn remote_read(&self, request: RemoteReadRequest<Block::Hash>) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<Block::Hash>) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker<Block: BlockT>: Send + Sync {
	/// Check remote header proof.
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<NumberFor<Block>>,
		header: Option<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Block::Header>;
	/// Check remote storage read proof.
	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Hash>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Hash>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<CallResult>;
}

/// Remote data checker.
pub struct LightDataChecker<S, E, F> {
	cht_size: u64,
	blockchain: Arc<Blockchain<S, F>>,
	executor: E,
}

impl<S, E, F> LightDataChecker<S, E, F> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<S, F>>, executor: E) -> Self {
		Self {
			cht_size: cht::SIZE,
			blockchain,
			executor,
		}
	}

	/// Create new light data checker with given cht size.
	#[cfg(test)]
	pub fn with_cht_size(cht_size: u64, blockchain: Arc<Blockchain<S, F>>, executor: E) -> Self {
		Self {
			cht_size,
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
		Block::Hash: From<[u8; 32]> + Into<[u8; 32]>,
		S: BlockchainStorage<Block>,
		E: CodeExecutor,
		F: Fetcher<Block>,
{
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<NumberFor<Block>>,
		remote_header: Option<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Block::Header> {
		let remote_header = remote_header.ok_or_else(|| ClientError::from(ClientErrorKind::InvalidHeaderProof))?;
		let remote_header_hash = remote_header.hash();
		let local_cht_root = self.blockchain.storage().cht_root(self.cht_size, request.block)?;
		cht::check_proof::<Block::Header>(local_cht_root, request.block, remote_header_hash, remote_proof)
			.map(|_| remote_header)
	}

	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Hash>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>> {
		let local_header = self.blockchain.header(BlockId::Hash(request.block))?;
		let local_header = local_header.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", request.block)))?;
		let local_state_root = *local_header.state_root();
		read_proof_check(local_state_root.into(), remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Hash>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<CallResult> {
		check_execution_proof(&*self.blockchain, &self.executor, request, remote_proof)
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
	use light::new_light_blockchain;
	use light::fetcher::{Fetcher, FetchChecker, LightDataChecker,
		RemoteCallRequest, RemoteHeaderRequest};
	use state_machine::Backend;
	use super::*;

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteHeaderResult = FutureResult<Header, ClientError>;
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_header(&self, _request: RemoteHeaderRequest<NumberFor<Block>>) -> Self::RemoteHeaderResult {
			err("Not implemented on test node".into())
		}

		fn remote_read(&self, _request: RemoteReadRequest<Hash>) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest<Hash>) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}
	}

	fn prepare_for_read_proof_check(insert_header: bool) -> (
		LightDataChecker<
			InMemoryBlockchain<Block>,
			executor::NativeExecutor<test_client::LocalExecutor>,
			OkCallFetcher>,
		Hash, Vec<Vec<u8>>, usize)
	{
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.authorities_at(&remote_block_id).unwrap().len();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, b":auth:len").unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		if insert_header {
			local_storage.insert(remote_block_hash, remote_block_header, None, None, true);
		}
		let local_executor = test_client::LocalExecutor::with_heap_pages(8, 8);
		let local_checker: LightDataChecker<
				InMemoryBlockchain<Block>,
				executor::NativeExecutor<test_client::LocalExecutor>,
				OkCallFetcher
			> = LightDataChecker::with_cht_size(4, new_light_blockchain(local_storage), local_executor);
		(local_checker, remote_block_hash, remote_read_proof, authorities_len)
	}

	fn prepare_for_header_proof_check(insert_cht: bool) -> (
		LightDataChecker<
			InMemoryBlockchain<Block>,
			executor::NativeExecutor<test_client::LocalExecutor>,
			OkCallFetcher>,
		Header, Vec<Vec<u8>>)
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
		if insert_cht {
			let local_cht_root = cht::compute_root::<Header, _>(4, 0, local_headers_hashes.into_iter()).unwrap();
			local_storage.insert_cht_root(1, local_cht_root);
		}
		let local_executor = test_client::LocalExecutor::with_heap_pages(8, 8);
		let local_checker: LightDataChecker<
				InMemoryBlockchain<Block>,
				executor::NativeExecutor<test_client::LocalExecutor>,
				OkCallFetcher
			> = LightDataChecker::with_cht_size(4, new_light_blockchain(local_storage), local_executor);
		(local_checker, remote_block_header, remote_header_proof)
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		let (local_checker, remote_block_hash, remote_read_proof, authorities_len) = prepare_for_read_proof_check(true);
		assert_eq!(local_checker.check_read_proof(&RemoteReadRequest {
			block: remote_block_hash,
			key: b":auth:len".to_vec(),
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}

	#[test]
	fn check_read_proof_fails_if_header_is_unknown() {
		let (local_checker, remote_block_hash, remote_read_proof, _) = prepare_for_read_proof_check(false);
		assert!(local_checker.check_read_proof(&RemoteReadRequest {
			block: remote_block_hash,
			key: b":auth:len".to_vec(),
		}, remote_read_proof).is_err());
	}

	#[test]
	fn header_proof_is_generated_and_checked() {
		let (local_checker, remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		assert_eq!(local_checker.check_header_proof(&RemoteHeaderRequest {
			block: 1,
		}, Some(remote_block_header.clone()), remote_header_proof).unwrap(), remote_block_header);
	}

	#[test]
	fn check_header_proof_fails_if_header_is_none() {
		let (local_checker, _, remote_header_proof) = prepare_for_header_proof_check(true);
		assert!(local_checker.check_header_proof(&RemoteHeaderRequest {
			block: 1,
		}, None, remote_header_proof).is_err());
	}

	#[test]
	fn check_header_proof_fails_if_local_cht_is_unknown() {
		let (local_checker, remote_block_header, remote_header_proof) = prepare_for_header_proof_check(false);
		assert!(local_checker.check_header_proof(&RemoteHeaderRequest {
			block: 1,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}

	#[test]
	fn check_header_proof_fails_if_invalid_header_provided() {
		let (local_checker, mut remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		remote_block_header.number = 100;
		assert!(local_checker.check_header_proof(&RemoteHeaderRequest {
			block: 1,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}
}
