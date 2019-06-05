// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use futures::IntoFuture;

use hash_db::{HashDB, Hasher};
use parity_codec::{Decode, Encode};
use primitives::{ChangesTrieConfiguration, convert_hash};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, Hash, HashFor, NumberFor,
	SimpleArithmetic, CheckedConversion,
};
use state_machine::{CodeExecutor, ChangesTrieRootsStorage, ChangesTrieAnchorBlockId,
	TrieBackend, read_proof_check, key_changes_proof_check,
	create_proof_check_backend_storage, read_child_proof_check};

use crate::cht;
use crate::error::{Error as ClientError, Result as ClientResult};
use crate::light::blockchain::{Blockchain, Storage as BlockchainStorage};
use crate::light::call_executor::check_execution_proof;

/// Remote call request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest<Header: HeaderT> {
	/// Call at state of given block.
	pub block: Header::Hash,
	/// Header of block at which call is performed.
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
	/// Header of block at which read is performed.
	pub header: Header,
	/// Storage key to read.
	pub key: Vec<u8>,
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
}

/// Remote storage read child request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteReadChildRequest<Header: HeaderT> {
	/// Read at state of given block.
	pub block: Header::Hash,
	/// Header of block at which read is performed.
	pub header: Header,
	/// Storage key for child.
	pub storage_key: Vec<u8>,
	/// Child storage key to read.
	pub key: Vec<u8>,
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
}

/// Remote key changes read request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemoteChangesRequest<Header: HeaderT> {
	/// Changes trie configuration.
	pub changes_trie_config: ChangesTrieConfiguration,
	/// Query changes from range of blocks, starting (and including) with this hash...
	pub first_block: (Header::Number, Header::Hash),
	/// ...ending (and including) with this hash. Should come after first_block and
	/// be the part of the same fork.
	pub last_block: (Header::Number, Header::Hash),
	/// Only use digests from blocks up to this hash. Should be last_block OR come
	/// after this block and be the part of the same fork.
	pub max_block: (Header::Number, Header::Hash),
	/// Known changes trie roots for the range of blocks [tries_roots.0..max_block].
	/// Proofs for roots of ascendants of tries_roots.0 are provided by the remote node.
	pub tries_roots: (Header::Number, Header::Hash, Vec<Header::Hash>),
	/// Storage key to read.
	pub key: Vec<u8>,
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
}

/// Key changes read proof.
#[derive(Debug, PartialEq, Eq)]
pub struct ChangesProof<Header: HeaderT> {
	/// Max block that has been used in changes query.
	pub max_block: Header::Number,
	/// All touched nodes of all changes tries.
	pub proof: Vec<Vec<u8>>,
	/// All changes tries roots that have been touched AND are missing from
	/// the requester' node. It is a map of block number => changes trie root.
	pub roots: BTreeMap<Header::Number, Header::Hash>,
	/// The proofs for all changes tries roots that have been touched AND are
	/// missing from the requester' node. It is a map of CHT number => proof.
	pub roots_proof: Vec<Vec<u8>>,
}

/// Remote block body request
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct RemoteBodyRequest<Header: HeaderT> {
	/// Header of the requested block body
	pub header: Header,
	/// Number of times to retry request. None means that default RETRY_COUNT is used.
	pub retry_count: Option<usize>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher<Block: BlockT>: Send + Sync {
	/// Remote header future.
	type RemoteHeaderResult: IntoFuture<Item = Block::Header, Error = ClientError>;
	/// Remote storage read future.
	type RemoteReadResult: IntoFuture<Item = Option<Vec<u8>>, Error = ClientError>;
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item = Vec<u8>, Error = ClientError>;
	/// Remote changes result future.
	type RemoteChangesResult: IntoFuture<Item = Vec<(NumberFor<Block>, u32)>, Error = ClientError>;
	/// Remote block body result future.
	type RemoteBodyResult: IntoFuture<Item = Vec<Block::Extrinsic>, Error = ClientError>;

	/// Fetch remote header.
	fn remote_header(&self, request: RemoteHeaderRequest<Block::Header>) -> Self::RemoteHeaderResult;
	/// Fetch remote storage value.
	fn remote_read(
		&self,
		request: RemoteReadRequest<Block::Header>
	) -> Self::RemoteReadResult;
	/// Fetch remote storage child value.
	fn remote_read_child(
		&self,
		request: RemoteReadChildRequest<Block::Header>
	) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<Block::Header>) -> Self::RemoteCallResult;
	/// Fetch remote changes ((block number, extrinsic index)) where given key has been changed
	/// at a given blocks range.
	fn remote_changes(&self, request: RemoteChangesRequest<Block::Header>) -> Self::RemoteChangesResult;
	/// Fetch remote block body
	fn remote_body(&self, request: RemoteBodyRequest<Block::Header>) -> Self::RemoteBodyResult;
}

/// Light client remote data checker.
///
/// Implementations of this trait should not use any prunable blockchain data
/// except that is passed to its methods.
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
	/// Check remote storage read proof.
	fn check_read_child_proof(
		&self,
		request: &RemoteReadChildRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Vec<u8>>;
	/// Check remote changes query proof.
	fn check_changes_proof(
		&self,
		request: &RemoteChangesRequest<Block::Header>,
		proof: ChangesProof<Block::Header>
	) -> ClientResult<Vec<(NumberFor<Block>, u32)>>;
	/// Check remote body proof.
	fn check_body_proof(
		&self,
		request: &RemoteBodyRequest<Block::Header>,
		body: Vec<Block::Extrinsic>
	) -> ClientResult<Vec<Block::Extrinsic>>;
}

/// Remote data checker.
pub struct LightDataChecker<E, H, B: BlockT, S: BlockchainStorage<B>, F> {
	blockchain: Arc<Blockchain<S, F>>,
	executor: E,
	_hasher: PhantomData<(B, H)>,
}

impl<E, H, B: BlockT, S: BlockchainStorage<B>, F> LightDataChecker<E, H, B, S, F> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<S, F>>, executor: E) -> Self {
		Self {
			blockchain, executor, _hasher: PhantomData
		}
	}

	/// Check remote changes query proof assuming that CHT-s are of given size.
	fn check_changes_proof_with_cht_size(
		&self,
		request: &RemoteChangesRequest<B::Header>,
		remote_proof: ChangesProof<B::Header>,
		cht_size: NumberFor<B>,
	) -> ClientResult<Vec<(NumberFor<B>, u32)>>
		where
			H: Hasher,
			H::Out: Ord,
	{
		// since we need roots of all changes tries for the range begin..max
		// => remote node can't use max block greater that one that we have passed
		if remote_proof.max_block > request.max_block.0 || remote_proof.max_block < request.last_block.0 {
			return Err(ClientError::ChangesTrieAccessFailed(format!(
				"Invalid max_block used by the remote node: {}. Local: {}..{}..{}",
				remote_proof.max_block, request.first_block.0, request.last_block.0, request.max_block.0,
			)).into());
		}

		// check if remote node has responded with extra changes trie roots proofs
		// all changes tries roots must be in range [request.first_block.0; request.tries_roots.0)
		let is_extra_first_root = remote_proof.roots.keys().next()
			.map(|first_root| *first_root < request.first_block.0
				|| *first_root >= request.tries_roots.0)
			.unwrap_or(false);
		let is_extra_last_root = remote_proof.roots.keys().next_back()
			.map(|last_root| *last_root >= request.tries_roots.0)
			.unwrap_or(false);
		if is_extra_first_root || is_extra_last_root {
			return Err(ClientError::ChangesTrieAccessFailed(format!(
				"Extra changes tries roots proofs provided by the remote node: [{:?}..{:?}]. Expected in range: [{}; {})",
				remote_proof.roots.keys().next(), remote_proof.roots.keys().next_back(),
				request.first_block.0, request.tries_roots.0,
			)).into());
		}

		// if request has been composed when some required headers were already pruned
		// => remote node has sent us CHT-based proof of required changes tries roots
		// => check that this proof is correct before proceeding with changes proof
		let remote_max_block = remote_proof.max_block;
		let remote_roots = remote_proof.roots;
		let remote_roots_proof = remote_proof.roots_proof;
		let remote_proof = remote_proof.proof;
		if !remote_roots.is_empty() {
			self.check_changes_tries_proof(
				cht_size,
				&remote_roots,
				remote_roots_proof,
			)?;
		}

		// and now check the key changes proof + get the changes
		key_changes_proof_check::<_, H, _>(
			&request.changes_trie_config,
			&RootsStorage {
				roots: (request.tries_roots.0, &request.tries_roots.2),
				prev_roots: remote_roots,
			},
			remote_proof,
			request.first_block.0,
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&request.last_block.1),
				number: request.last_block.0,
			},
			remote_max_block,
			&request.key)
		.map_err(|err| ClientError::ChangesTrieAccessFailed(err))
	}

	/// Check CHT-based proof for changes tries roots.
	fn check_changes_tries_proof(
		&self,
		cht_size: NumberFor<B>,
		remote_roots: &BTreeMap<NumberFor<B>, B::Hash>,
		remote_roots_proof: Vec<Vec<u8>>,
	) -> ClientResult<()>
		where
			H: Hasher,
			H::Out: Ord,
	{
		// all the checks are sharing the same storage
		let storage = create_proof_check_backend_storage(remote_roots_proof);

		// we remote_roots.keys() are sorted => we can use this to group changes tries roots
		// that are belongs to the same CHT
		let blocks = remote_roots.keys().cloned();
		cht::for_each_cht_group::<B::Header, _, _, _>(cht_size, blocks, |mut storage, _, cht_blocks| {
			// get local changes trie CHT root for given CHT
			// it should be there, because it is never pruned AND request has been composed
			// when required header has been pruned (=> replaced with CHT)
			let first_block = cht_blocks.first().cloned()
				.expect("for_each_cht_group never calls callback with empty groups");
			let local_cht_root = self.blockchain.storage().changes_trie_cht_root(cht_size, first_block)?;

			// check changes trie root for every block within CHT range
			for block in cht_blocks {
				// check if the proofs storage contains the root
				// normally this happens in when the proving backend is created, but since
				// we share the storage for multiple checks, do it here
				let mut cht_root = H::Out::default();
				cht_root.as_mut().copy_from_slice(local_cht_root.as_ref());
				if !storage.contains(&cht_root, &[]) {
					return Err(ClientError::InvalidCHTProof.into());
				}

				// check proof for single changes trie root
				let proving_backend = TrieBackend::new(storage, cht_root);
				let remote_changes_trie_root = remote_roots[&block];
				cht::check_proof_on_proving_backend::<B::Header, H>(
					local_cht_root,
					block,
					remote_changes_trie_root,
					&proving_backend)?;

				// and return the storage to use in following checks
				storage = proving_backend.into_storage();
			}

			Ok(storage)
		}, storage)
	}
}

impl<E, Block, H, S, F> FetchChecker<Block> for LightDataChecker<E, H, Block, S, F>
	where
		Block: BlockT,
		E: CodeExecutor<H>,
		H: Hasher,
		H::Out: Ord + 'static,
		S: BlockchainStorage<Block>,
		F: Send + Sync,
{
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<Block::Header>,
		remote_header: Option<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Block::Header> {
		let remote_header = remote_header.ok_or_else(||
			ClientError::from(ClientError::InvalidCHTProof))?;
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
		read_proof_check::<H>(convert_hash(request.header.state_root()), remote_proof, &request.key)
			.map_err(Into::into)
	}

	fn check_read_child_proof(
		&self,
		request: &RemoteReadChildRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Option<Vec<u8>>> {
		read_child_proof_check::<H>(
			convert_hash(request.header.state_root()),
			remote_proof,
			&request.storage_key,
			&request.key)
			.map_err(Into::into)
	}

	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: Vec<Vec<u8>>
	) -> ClientResult<Vec<u8>> {
		check_execution_proof::<_, _, H>(&self.executor, request, remote_proof)
	}

	fn check_changes_proof(
		&self,
		request: &RemoteChangesRequest<Block::Header>,
		remote_proof: ChangesProof<Block::Header>
	) -> ClientResult<Vec<(NumberFor<Block>, u32)>> {
		self.check_changes_proof_with_cht_size(request, remote_proof, cht::size())
	}

	fn check_body_proof(
		&self,
		request: &RemoteBodyRequest<Block::Header>,
		body: Vec<Block::Extrinsic>
	) -> ClientResult<Vec<Block::Extrinsic>> {

		// TODO: #2621
		let	extrinsics_root = HashFor::<Block>::ordered_trie_root(body.iter().map(Encode::encode));
		if *request.header.extrinsics_root() == extrinsics_root {
			Ok(body)
		} else {
			Err(format!("RemoteBodyRequest: invalid extrinsics root expected: {} but got {}",
				*request.header.extrinsics_root(),
				extrinsics_root,
			).into())
		}

	}
}

/// A view of BTreeMap<Number, Hash> as a changes trie roots storage.
struct RootsStorage<'a, Number: SimpleArithmetic, Hash: 'a> {
	roots: (Number, &'a [Hash]),
	prev_roots: BTreeMap<Number, Hash>,
}

impl<'a, H, Number, Hash> ChangesTrieRootsStorage<H, Number> for RootsStorage<'a, Number, Hash>
	where
		H: Hasher,
		Number: ::std::fmt::Display + Clone + SimpleArithmetic + Encode + Decode + Send + Sync + 'static,
		Hash: 'a + Send + Sync + Clone + AsRef<[u8]>,
{
	fn build_anchor(
		&self,
		_hash: H::Out,
	) -> Result<state_machine::ChangesTrieAnchorBlockId<H::Out, Number>, String> {
		Err("build_anchor is only called when building block".into())
	}

	fn root(
		&self,
		_anchor: &ChangesTrieAnchorBlockId<H::Out, Number>,
		block: Number,
	) -> Result<Option<H::Out>, String> {
		// we can't ask for roots from parallel forks here => ignore anchor
		let root = if block < self.roots.0 {
			self.prev_roots.get(&Number::unique_saturated_from(block)).cloned()
		} else {
			let index: Option<usize> = block.checked_sub(&self.roots.0).and_then(|index| index.checked_into());
			match index {
				Some(index) => self.roots.1.get(index as usize).cloned(),
				None => None,
			}
		};

		Ok(root.map(|root| {
			let mut hasher_root: H::Out = Default::default();
			hasher_root.as_mut().copy_from_slice(root.as_ref());
			hasher_root
		}))
	}
}

#[cfg(test)]
pub mod tests {
	use futures::future::{ok, err, FutureResult};
	use parking_lot::Mutex;
	use parity_codec::Decode;
	use crate::client::tests::prepare_client_with_key_changes;
	use executor::{self, NativeExecutionDispatch};
	use crate::error::Error as ClientError;
	use test_client::{
		self, TestClient, blockchain::HeaderBackend, AccountKeyring,
		runtime::{self, Hash, Block, Header, Extrinsic}
	};
	use consensus::BlockOrigin;

	use crate::in_mem::{Blockchain as InMemoryBlockchain};
	use crate::light::fetcher::{Fetcher, FetchChecker, LightDataChecker,
		RemoteCallRequest, RemoteHeaderRequest};
	use crate::light::blockchain::tests::{DummyStorage, DummyBlockchain};
	use primitives::{blake2_256, Blake2Hasher, H256};
	use primitives::storage::{StorageKey, well_known_keys};
	use runtime_primitives::generic::BlockId;
	use state_machine::Backend;
	use super::*;

	pub type OkCallFetcher = Mutex<Vec<u8>>;

	fn not_implemented_in_tests<T, E>() -> FutureResult<T, E>
	where
		E: std::convert::From<&'static str>,
	{
		err("Not implemented on test node".into())
	}

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteHeaderResult = FutureResult<Header, ClientError>;
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<Vec<u8>, ClientError>;
		type RemoteChangesResult = FutureResult<Vec<(NumberFor<Block>, u32)>, ClientError>;
		type RemoteBodyResult = FutureResult<Vec<Extrinsic>, ClientError>;

		fn remote_header(&self, _request: RemoteHeaderRequest<Header>) -> Self::RemoteHeaderResult {
			not_implemented_in_tests()
		}

		fn remote_read(&self, _request: RemoteReadRequest<Header>) -> Self::RemoteReadResult {
			not_implemented_in_tests()
		}

		fn remote_read_child(&self, _request: RemoteReadChildRequest<Header>) -> Self::RemoteReadResult {
			not_implemented_in_tests()
		}

		fn remote_call(&self, _request: RemoteCallRequest<Header>) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}

		fn remote_changes(&self, _request: RemoteChangesRequest<Header>) -> Self::RemoteChangesResult {
			not_implemented_in_tests()
		}

		fn remote_body(&self, _request: RemoteBodyRequest<Header>) -> Self::RemoteBodyResult {
			not_implemented_in_tests()
		}
	}

	type TestChecker = LightDataChecker<
		executor::NativeExecutor<test_client::LocalExecutor>,
		Blake2Hasher,
		Block,
		DummyStorage,
		OkCallFetcher,
	>;

	fn prepare_for_read_proof_check() -> (TestChecker, Header, Vec<Vec<u8>>, u32) {
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.storage(&remote_block_id, &StorageKey(well_known_keys::AUTHORITY_COUNT.to_vec()))
			.unwrap()
			.and_then(|v| Decode::decode(&mut &v.0[..])).unwrap();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, well_known_keys::AUTHORITY_COUNT).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		local_storage.insert(
			remote_block_hash,
			remote_block_header.clone(),
			None,
			None,
			crate::backend::NewBlockState::Final,
		).unwrap();
		let local_executor = test_client::LocalExecutor::new(None);
		let local_checker = LightDataChecker::new(Arc::new(DummyBlockchain::new(DummyStorage::new())), local_executor);
		(local_checker, remote_block_header, remote_read_proof, authorities_len)
	}

	fn prepare_for_header_proof_check(insert_cht: bool) -> (TestChecker, Hash, Header, Vec<Vec<u8>>) {
		// prepare remote client
		let remote_client = test_client::new();
		let mut local_headers_hashes = Vec::new();
		for i in 0..4 {
			let builder = remote_client.new_block(Default::default()).unwrap();
			remote_client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
			local_headers_hashes.push(remote_client.block_hash(i + 1)
				.map_err(|_| ClientError::Backend("TestError".into())));
		}

		// 'fetch' header proof from remote node
		let remote_block_id = BlockId::Number(1);
		let (remote_block_header, remote_header_proof) = remote_client.header_proof_with_cht_size(&remote_block_id, 4).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		let local_cht_root = cht::compute_root::<Header, Blake2Hasher, _>(4, 0, local_headers_hashes).unwrap();
		if insert_cht {
			local_storage.insert_cht_root(1, local_cht_root);
		}
		let local_executor = test_client::LocalExecutor::new(None);
		let local_checker = LightDataChecker::new(Arc::new(DummyBlockchain::new(DummyStorage::new())), local_executor);
		(local_checker, local_cht_root, remote_block_header, remote_header_proof)
	}

	fn header_with_computed_extrinsics_root(extrinsics: Vec<Extrinsic>) -> Header {
		let extrinsics_root =
			trie::ordered_trie_root::<Blake2Hasher, _, _>(extrinsics.iter().map(Encode::encode));

		// only care about `extrinsics_root`
		Header::new(0, extrinsics_root, H256::zero(), H256::zero(), Default::default())
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		let (local_checker, remote_block_header, remote_read_proof, authorities_len) = prepare_for_read_proof_check();
		assert_eq!((&local_checker as &dyn FetchChecker<Block>).check_read_proof(&RemoteReadRequest::<Header> {
			block: remote_block_header.hash(),
			header: remote_block_header,
			key: well_known_keys::AUTHORITY_COUNT.to_vec(),
			retry_count: None,
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}

	#[test]
	fn header_proof_is_generated_and_checked() {
		let (local_checker, local_cht_root, remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		assert_eq!((&local_checker as &dyn FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: local_cht_root,
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).unwrap(), remote_block_header);
	}

	#[test]
	fn check_header_proof_fails_if_cht_root_is_invalid() {
		let (local_checker, _, mut remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		remote_block_header.number = 100;
		assert!((&local_checker as &dyn FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: Default::default(),
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}

	#[test]
	fn check_header_proof_fails_if_invalid_header_provided() {
		let (local_checker, local_cht_root, mut remote_block_header, remote_header_proof) = prepare_for_header_proof_check(true);
		remote_block_header.number = 100;
		assert!((&local_checker as &dyn FetchChecker<Block>).check_header_proof(&RemoteHeaderRequest::<Header> {
			cht_root: local_cht_root,
			block: 1,
			retry_count: None,
		}, Some(remote_block_header.clone()), remote_header_proof).is_err());
	}

	#[test]
	fn changes_proof_is_generated_and_checked_when_headers_are_not_pruned() {
		let (remote_client, local_roots, test_cases) = prepare_client_with_key_changes();
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			test_client::LocalExecutor::new(None)
		);
		let local_checker = &local_checker as &dyn FetchChecker<Block>;
		let max = remote_client.info().chain.best_number;
		let max_hash = remote_client.info().chain.best_hash;

		for (index, (begin, end, key, expected_result)) in test_cases.into_iter().enumerate() {
			let begin_hash = remote_client.block_hash(begin).unwrap().unwrap();
			let end_hash = remote_client.block_hash(end).unwrap().unwrap();

			// 'fetch' changes proof from remote node
			let key = StorageKey(key);
			let remote_proof = remote_client.key_changes_proof(
				begin_hash, end_hash, begin_hash, max_hash, &key
			).unwrap();

			// check proof on local client
			let local_roots_range = local_roots.clone()[(begin - 1) as usize..].to_vec();
			let request = RemoteChangesRequest::<Header> {
				changes_trie_config: runtime::changes_trie_config(),
				first_block: (begin, begin_hash),
				last_block: (end, end_hash),
				max_block: (max, max_hash),
				tries_roots: (begin, begin_hash, local_roots_range),
				key: key.0,
				retry_count: None,
			};
			let local_result = local_checker.check_changes_proof(&request, ChangesProof {
				max_block: remote_proof.max_block,
				proof: remote_proof.proof,
				roots: remote_proof.roots,
				roots_proof: remote_proof.roots_proof,
			}).unwrap();

			// ..and ensure that result is the same as on remote node
			match local_result == expected_result {
				true => (),
				false => panic!(format!("Failed test {}: local = {:?}, expected = {:?}",
					index, local_result, expected_result)),
			}
		}
	}

	#[test]
	fn changes_proof_is_generated_and_checked_when_headers_are_pruned() {
		// we're testing this test case here:
		// (1, 4, dave.clone(), vec![(4, 0), (1, 1), (1, 0)]),
		let (remote_client, remote_roots, _) = prepare_client_with_key_changes();
		let dave = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Dave.into())).to_vec();
		let dave = StorageKey(dave);

		// 'fetch' changes proof from remote node:
		// we're fetching changes for range b1..b4
		// we do not know changes trie roots before b3 (i.e. we only know b3+b4)
		// but we have changes trie CHT root for b1...b4
		let b1 = remote_client.block_hash_from_id(&BlockId::Number(1)).unwrap().unwrap();
		let b3 = remote_client.block_hash_from_id(&BlockId::Number(3)).unwrap().unwrap();
		let b4 = remote_client.block_hash_from_id(&BlockId::Number(4)).unwrap().unwrap();
		let remote_proof = remote_client.key_changes_proof_with_cht_size(
			b1, b4, b3, b4, &dave, 4
		).unwrap();

		// prepare local checker, having a root of changes trie CHT#0
		let local_cht_root = cht::compute_root::<Header, Blake2Hasher, _>(4, 0, remote_roots.iter().cloned().map(|ct| Ok(Some(ct)))).unwrap();
		let mut local_storage = DummyStorage::new();
		local_storage.changes_tries_cht_roots.insert(0, local_cht_root);
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(local_storage)),
			test_client::LocalExecutor::new(None)
		);

		// check proof on local client
		let request = RemoteChangesRequest::<Header> {
			changes_trie_config: runtime::changes_trie_config(),
			first_block: (1, b1),
			last_block: (4, b4),
			max_block: (4, b4),
			tries_roots: (3, b3, vec![remote_roots[2].clone(), remote_roots[3].clone()]),
			key: dave.0,
			retry_count: None,
		};
		let local_result = local_checker.check_changes_proof_with_cht_size(&request, ChangesProof {
			max_block: remote_proof.max_block,
			proof: remote_proof.proof,
			roots: remote_proof.roots,
			roots_proof: remote_proof.roots_proof,
		}, 4).unwrap();

		assert_eq!(local_result, vec![(4, 0), (1, 1), (1, 0)]);
	}

	#[test]
	fn check_changes_proof_fails_if_proof_is_wrong() {
		let (remote_client, local_roots, test_cases) = prepare_client_with_key_changes();
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			test_client::LocalExecutor::new(None)
		);
		let local_checker = &local_checker as &dyn FetchChecker<Block>;
		let max = remote_client.info().chain.best_number;
		let max_hash = remote_client.info().chain.best_hash;

		let (begin, end, key, _) = test_cases[0].clone();
		let begin_hash = remote_client.block_hash(begin).unwrap().unwrap();
		let end_hash = remote_client.block_hash(end).unwrap().unwrap();

		// 'fetch' changes proof from remote node
		let key = StorageKey(key);
		let remote_proof = remote_client.key_changes_proof(
			begin_hash, end_hash, begin_hash, max_hash, &key).unwrap();

		let local_roots_range = local_roots.clone()[(begin - 1) as usize..].to_vec();
		let request = RemoteChangesRequest::<Header> {
			changes_trie_config: runtime::changes_trie_config(),
			first_block: (begin, begin_hash),
			last_block: (end, end_hash),
			max_block: (max, max_hash),
			tries_roots: (begin, begin_hash, local_roots_range.clone()),
			key: key.0,
			retry_count: None,
		};

		// check proof on local client using max from the future
		assert!(local_checker.check_changes_proof(&request, ChangesProof {
			max_block: remote_proof.max_block + 1,
			proof: remote_proof.proof.clone(),
			roots: remote_proof.roots.clone(),
			roots_proof: remote_proof.roots_proof.clone(),
		}).is_err());

		// check proof on local client using broken proof
		assert!(local_checker.check_changes_proof(&request, ChangesProof {
			max_block: remote_proof.max_block,
			proof: local_roots_range.clone().into_iter().map(|v| v.as_ref().to_vec()).collect(),
			roots: remote_proof.roots,
			roots_proof: remote_proof.roots_proof,
		}).is_err());

		// extra roots proofs are provided
		assert!(local_checker.check_changes_proof(&request, ChangesProof {
			max_block: remote_proof.max_block,
			proof: remote_proof.proof.clone(),
			roots: vec![(begin - 1, Default::default())].into_iter().collect(),
			roots_proof: vec![],
		}).is_err());
		assert!(local_checker.check_changes_proof(&request, ChangesProof {
			max_block: remote_proof.max_block,
			proof: remote_proof.proof.clone(),
			roots: vec![(end + 1, Default::default())].into_iter().collect(),
			roots_proof: vec![],
		}).is_err());
	}

	#[test]
	fn check_changes_tries_proof_fails_if_proof_is_wrong() {
		// we're testing this test case here:
		// (1, 4, dave.clone(), vec![(4, 0), (1, 1), (1, 0)]),
		let (remote_client, remote_roots, _) = prepare_client_with_key_changes();
		let local_cht_root = cht::compute_root::<Header, Blake2Hasher, _>(
			4, 0, remote_roots.iter().cloned().map(|ct| Ok(Some(ct)))).unwrap();
		let dave = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Dave.into())).to_vec();
		let dave = StorageKey(dave);

		// 'fetch' changes proof from remote node:
		// we're fetching changes for range b1..b4
		// we do not know changes trie roots before b3 (i.e. we only know b3+b4)
		// but we have changes trie CHT root for b1...b4
		let b1 = remote_client.block_hash_from_id(&BlockId::Number(1)).unwrap().unwrap();
		let b3 = remote_client.block_hash_from_id(&BlockId::Number(3)).unwrap().unwrap();
		let b4 = remote_client.block_hash_from_id(&BlockId::Number(4)).unwrap().unwrap();
		let remote_proof = remote_client.key_changes_proof_with_cht_size(
			b1, b4, b3, b4, &dave, 4
		).unwrap();

		// fails when changes trie CHT is missing from the local db
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			test_client::LocalExecutor::new(None)
		);
		assert!(local_checker.check_changes_tries_proof(4, &remote_proof.roots,
			remote_proof.roots_proof.clone()).is_err());

		// fails when proof is broken
		let mut local_storage = DummyStorage::new();
		local_storage.changes_tries_cht_roots.insert(0, local_cht_root);
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(local_storage)),
			test_client::LocalExecutor::new(None)
		);
		assert!(local_checker.check_changes_tries_proof(4, &remote_proof.roots, vec![]).is_err());
	}

	#[test]
	fn check_body_proof_faulty() {
		let header = header_with_computed_extrinsics_root(
			vec![Extrinsic::IncludeData(vec![1, 2, 3, 4])]
		);
		let block = Block::new(header.clone(), Vec::new());

		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			test_client::LocalExecutor::new(None)
		);

		let body_request = RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		};

		assert!(
			local_checker.check_body_proof(&body_request, block.extrinsics).is_err(),
			"vec![1, 2, 3, 4] != vec![]"
		);
	}

	#[test]
	fn check_body_proof_of_same_data_should_succeed() {
		let extrinsics = vec![Extrinsic::IncludeData(vec![1, 2, 3, 4, 5, 6, 7, 8, 255])];

		let header = header_with_computed_extrinsics_root(extrinsics.clone());
		let block = Block::new(header.clone(), extrinsics);

		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			test_client::LocalExecutor::new(None)
		);

		let body_request = RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		};

		assert!(local_checker.check_body_proof(&body_request, block.extrinsics).is_ok());
	}
}
