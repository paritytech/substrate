// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
use std::collections::{BTreeMap, HashMap};
use std::marker::PhantomData;

use hash_db::{HashDB, Hasher, EMPTY_PREFIX};
use codec::{Decode, Encode};
use sp_core::{convert_hash, traits::CodeExecutor};
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, Hash, HashFor, NumberFor,
	AtLeast32Bit, CheckedConversion,
};
use sp_state_machine::{
	ChangesTrieRootsStorage, ChangesTrieAnchorBlockId, ChangesTrieConfigurationRange,
	InMemoryChangesTrieStorage, TrieBackend, read_proof_check, key_changes_proof_check_with_db,
	read_child_proof_check,
};
pub use sp_state_machine::StorageProof;
use sp_blockchain::{Error as ClientError, Result as ClientResult};

use crate::cht;
pub use sc_client_api::{
	light::{
		RemoteCallRequest, RemoteHeaderRequest, RemoteReadRequest, RemoteReadChildRequest,
		RemoteChangesRequest, ChangesProof, RemoteBodyRequest, Fetcher, FetchChecker,
		Storage as BlockchainStorage,
	},
};
use crate::light::blockchain::{Blockchain};
use crate::light::call_executor::check_execution_proof;

/// Remote data checker.
pub struct LightDataChecker<E, H, B: BlockT, S: BlockchainStorage<B>> {
	blockchain: Arc<Blockchain<S>>,
	executor: E,
	_hasher: PhantomData<(B, H)>,
}

impl<E, H, B: BlockT, S: BlockchainStorage<B>> LightDataChecker<E, H, B, S> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<S>>, executor: E) -> Self {
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
			H::Out: Ord + codec::Codec,
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
		let mut result = Vec::new();
		let proof_storage = InMemoryChangesTrieStorage::with_proof(remote_proof);
		for config_range in &request.changes_trie_configs {
			let result_range = key_changes_proof_check_with_db::<H, _>(
				ChangesTrieConfigurationRange {
					config: config_range.config.as_ref().ok_or(ClientError::ChangesTriesNotSupported)?,
					zero: config_range.zero.0,
					end: config_range.end.map(|(n, _)| n),
				},
				&RootsStorage {
					roots: (request.tries_roots.0, &request.tries_roots.2),
					prev_roots: &remote_roots,
				},
				&proof_storage,
				request.first_block.0,
				&ChangesTrieAnchorBlockId {
					hash: convert_hash(&request.last_block.1),
					number: request.last_block.0,
				},
				remote_max_block,
				request.storage_key.as_ref().map(Vec::as_slice),
				&request.key)
			.map_err(|err| ClientError::ChangesTrieAccessFailed(err))?;
			result.extend(result_range);
		}

		Ok(result)
	}

	/// Check CHT-based proof for changes tries roots.
	fn check_changes_tries_proof(
		&self,
		cht_size: NumberFor<B>,
		remote_roots: &BTreeMap<NumberFor<B>, B::Hash>,
		remote_roots_proof: StorageProof,
	) -> ClientResult<()>
		where
			H: Hasher,
			H::Out: Ord + codec::Codec,
	{
		// all the checks are sharing the same storage
		let storage = remote_roots_proof.into_memory_db();

		// remote_roots.keys() are sorted => we can use this to group changes tries roots
		// that are belongs to the same CHT
		let blocks = remote_roots.keys().cloned();
		cht::for_each_cht_group::<B::Header, _, _, _>(cht_size, blocks, |mut storage, _, cht_blocks| {
			// get local changes trie CHT root for given CHT
			// it should be there, because it is never pruned AND request has been composed
			// when required header has been pruned (=> replaced with CHT)
			let first_block = cht_blocks.first().cloned()
				.expect("for_each_cht_group never calls callback with empty groups");
			let local_cht_root = self.blockchain.storage().changes_trie_cht_root(cht_size, first_block)?
				.ok_or(ClientError::InvalidCHTProof)?;

			// check changes trie root for every block within CHT range
			for block in cht_blocks {
				// check if the proofs storage contains the root
				// normally this happens in when the proving backend is created, but since
				// we share the storage for multiple checks, do it here
				let mut cht_root = H::Out::default();
				cht_root.as_mut().copy_from_slice(local_cht_root.as_ref());
				if !storage.contains(&cht_root, EMPTY_PREFIX) {
					return Err(ClientError::InvalidCHTProof.into());
				}

				// check proof for single changes trie root
				let proving_backend = TrieBackend::new(storage, cht_root);
				let remote_changes_trie_root = remote_roots[&block];
				cht::check_proof_on_proving_backend::<B::Header, H>(
					local_cht_root,
					block,
					remote_changes_trie_root,
					&proving_backend,
				)?;

				// and return the storage to use in following checks
				storage = proving_backend.into_storage();
			}

			Ok(storage)
		}, storage)
	}
}

impl<E, Block, H, S> FetchChecker<Block> for LightDataChecker<E, H, Block, S>
	where
		Block: BlockT,
		E: CodeExecutor + Clone + 'static,
		H: Hasher,
		H::Out: Ord + codec::Codec + 'static,
		S: BlockchainStorage<Block>,
{
	fn check_header_proof(
		&self,
		request: &RemoteHeaderRequest<Block::Header>,
		remote_header: Option<Block::Header>,
		remote_proof: StorageProof,
	) -> ClientResult<Block::Header> {
		let remote_header = remote_header.ok_or_else(||
			ClientError::from(ClientError::InvalidCHTProof))?;
		let remote_header_hash = remote_header.hash();
		cht::check_proof::<Block::Header, H>(
			request.cht_root,
			request.block,
			remote_header_hash,
			remote_proof,
		).map(|_| remote_header)
	}

	fn check_read_proof(
		&self,
		request: &RemoteReadRequest<Block::Header>,
		remote_proof: StorageProof,
	) -> ClientResult<HashMap<Vec<u8>, Option<Vec<u8>>>> {
		read_proof_check::<H, _>(
			convert_hash(request.header.state_root()),
			remote_proof,
			request.keys.iter(),
		).map_err(Into::into)
	}

	fn check_read_child_proof(
		&self,
		request: &RemoteReadChildRequest<Block::Header>,
		remote_proof: StorageProof,
	) -> ClientResult<HashMap<Vec<u8>, Option<Vec<u8>>>> {
		read_child_proof_check::<H, _>(
			convert_hash(request.header.state_root()),
			remote_proof,
			&request.storage_key,
			request.keys.iter(),
		).map_err(Into::into)
	}

	fn check_execution_proof(
		&self,
		request: &RemoteCallRequest<Block::Header>,
		remote_proof: StorageProof,
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
		let extrinsics_root = HashFor::<Block>::ordered_trie_root(
			body.iter().map(Encode::encode).collect(),
		);
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
struct RootsStorage<'a, Number: AtLeast32Bit, Hash: 'a> {
	roots: (Number, &'a [Hash]),
	prev_roots: &'a BTreeMap<Number, Hash>,
}

impl<'a, H, Number, Hash> ChangesTrieRootsStorage<H, Number> for RootsStorage<'a, Number, Hash>
	where
		H: Hasher,
		Number: std::fmt::Display + std::hash::Hash + Clone + AtLeast32Bit + Encode + Decode + Send + Sync + 'static,
		Hash: 'a + Send + Sync + Clone + AsRef<[u8]>,
{
	fn build_anchor(
		&self,
		_hash: H::Out,
	) -> Result<sp_state_machine::ChangesTrieAnchorBlockId<H::Out, Number>, String> {
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
	use codec::Decode;
	use crate::client::tests::prepare_client_with_key_changes;
	use sc_executor::{NativeExecutor, WasmExecutionMethod};
	use sp_blockchain::Error as ClientError;
	use sc_client_api::backend::NewBlockState;
	use substrate_test_runtime_client::{
		blockchain::HeaderBackend, AccountKeyring, ClientBlockImportExt,
		runtime::{self, Hash, Block, Header, Extrinsic}
	};
	use sp_consensus::BlockOrigin;

	use crate::in_mem::Blockchain as InMemoryBlockchain;
	use crate::light::fetcher::{FetchChecker, LightDataChecker, RemoteHeaderRequest};
	use crate::light::blockchain::tests::{DummyStorage, DummyBlockchain};
	use sp_core::{blake2_256, ChangesTrieConfiguration, H256};
	use sp_core::storage::{well_known_keys, StorageKey, ChildInfo};
	use sp_runtime::{generic::BlockId, traits::BlakeTwo256};
	use sp_state_machine::Backend;
	use super::*;
	use sc_client_api::{StorageProvider, ProofProvider};

	const CHILD_INFO_1: ChildInfo<'static> = ChildInfo::new_default(b"unique_id_1");

	type TestChecker = LightDataChecker<
		NativeExecutor<substrate_test_runtime_client::LocalExecutor>,
		BlakeTwo256,
		Block,
		DummyStorage,
	>;

	fn local_executor() -> NativeExecutor<substrate_test_runtime_client::LocalExecutor> {
		NativeExecutor::new(WasmExecutionMethod::Interpreted, None)
	}

	fn prepare_for_read_proof_check() -> (TestChecker, Header, StorageProof, u32) {
		// prepare remote client
		let remote_client = substrate_test_runtime_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap()
			.storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let heap_pages = remote_client.storage(&remote_block_id, &StorageKey(well_known_keys::HEAP_PAGES.to_vec()))
			.unwrap()
			.and_then(|v| Decode::decode(&mut &v.0[..]).ok()).unwrap();
		let remote_read_proof = remote_client.read_proof(
			&remote_block_id,
			&mut std::iter::once(well_known_keys::HEAP_PAGES),
		).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		local_storage.insert(
			remote_block_hash,
			remote_block_header.clone(),
			None,
			None,
			NewBlockState::Final,
		).unwrap();
		let local_checker = LightDataChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			local_executor()
		);
		(local_checker, remote_block_header, remote_read_proof, heap_pages)
	}

	fn prepare_for_read_child_proof_check() -> (TestChecker, Header, StorageProof, Vec<u8>) {
		use substrate_test_runtime_client::DefaultTestClientBuilderExt;
		use substrate_test_runtime_client::TestClientBuilderExt;
		// prepare remote client
		let remote_client = substrate_test_runtime_client::TestClientBuilder::new()
			.add_extra_child_storage(
				b":child_storage:default:child1".to_vec(),
				CHILD_INFO_1,
				b"key1".to_vec(),
				b"value1".to_vec(),
			).build();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap()
			.storage_root(::std::iter::empty()).0.into();

		// 'fetch' child read proof from remote node
		let child_value = remote_client.child_storage(
			&remote_block_id,
			&StorageKey(b":child_storage:default:child1".to_vec()),
			CHILD_INFO_1,
			&StorageKey(b"key1".to_vec()),
		).unwrap().unwrap().0;
		assert_eq!(b"value1"[..], child_value[..]);
		let remote_read_proof = remote_client.read_child_proof(
			&remote_block_id,
			b":child_storage:default:child1",
			CHILD_INFO_1,
			&mut std::iter::once("key1".as_bytes()),
		).unwrap();

		// check locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		local_storage.insert(
			remote_block_hash,
			remote_block_header.clone(),
			None,
			None,
			NewBlockState::Final,
		).unwrap();
		let local_checker = LightDataChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			local_executor(),
		);
		(local_checker, remote_block_header, remote_read_proof, child_value)
	}

	fn prepare_for_header_proof_check(insert_cht: bool) -> (TestChecker, Hash, Header, StorageProof) {
		// prepare remote client
		let mut remote_client = substrate_test_runtime_client::new();
		let mut local_headers_hashes = Vec::new();
		for i in 0..4 {
			let block = remote_client.new_block(Default::default()).unwrap().build().unwrap().block;
			remote_client.import(BlockOrigin::Own, block).unwrap();
			local_headers_hashes.push(
				remote_client.block_hash(i + 1)
					.map_err(|_| ClientError::Backend("TestError".into()))
			);
		}

		// 'fetch' header proof from remote node
		let remote_block_id = BlockId::Number(1);
		let (remote_block_header, remote_header_proof) = remote_client.header_proof_with_cht_size(&remote_block_id, 4).unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		let local_cht_root = cht::compute_root::<Header, BlakeTwo256, _>(4, 0, local_headers_hashes).unwrap();
		if insert_cht {
			local_storage.insert_cht_root(1, local_cht_root);
		}
		let local_checker = LightDataChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			local_executor(),
		);
		(local_checker, local_cht_root, remote_block_header, remote_header_proof)
	}

	fn header_with_computed_extrinsics_root(extrinsics: Vec<Extrinsic>) -> Header {
		use sp_trie::{TrieConfiguration, trie_types::Layout};
		let iter = extrinsics.iter().map(Encode::encode);
		let extrinsics_root = Layout::<BlakeTwo256>::ordered_trie_root(iter);

		// only care about `extrinsics_root`
		Header::new(0, extrinsics_root, H256::zero(), H256::zero(), Default::default())
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		let (local_checker, remote_block_header, remote_read_proof, heap_pages) = prepare_for_read_proof_check();
		assert_eq!((&local_checker as &dyn FetchChecker<Block>).check_read_proof(&RemoteReadRequest::<Header> {
			block: remote_block_header.hash(),
			header: remote_block_header,
			keys: vec![well_known_keys::HEAP_PAGES.to_vec()],
			retry_count: None,
		}, remote_read_proof).unwrap().remove(well_known_keys::HEAP_PAGES).unwrap().unwrap()[0], heap_pages as u8);
	}

	#[test]
	fn storage_child_read_proof_is_generated_and_checked() {
		let (
			local_checker,
			remote_block_header,
			remote_read_proof,
			result,
		) = prepare_for_read_child_proof_check();
		let child_infos = CHILD_INFO_1.info();
		assert_eq!((&local_checker as &dyn FetchChecker<Block>).check_read_child_proof(
			&RemoteReadChildRequest::<Header> {
				block: remote_block_header.hash(),
				header: remote_block_header,
				storage_key: b":child_storage:default:child1".to_vec(),
				child_info: child_infos.0.to_vec(),
				child_type: child_infos.1,
				keys: vec![b"key1".to_vec()],
				retry_count: None,
			},
			remote_read_proof
		).unwrap().remove(b"key1".as_ref()).unwrap().unwrap(), result);
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
			local_executor(),
		);
		let local_checker = &local_checker as &dyn FetchChecker<Block>;
		let max = remote_client.chain_info().best_number;
		let max_hash = remote_client.chain_info().best_hash;

		for (index, (begin, end, key, expected_result)) in test_cases.into_iter().enumerate() {
			let begin_hash = remote_client.block_hash(begin).unwrap().unwrap();
			let end_hash = remote_client.block_hash(end).unwrap().unwrap();

			// 'fetch' changes proof from remote node
			let key = StorageKey(key);
			let remote_proof = remote_client.key_changes_proof(
				begin_hash, end_hash, begin_hash, max_hash, None, &key
			).unwrap();

			// check proof on local client
			let local_roots_range = local_roots.clone()[(begin - 1) as usize..].to_vec();
			let config = ChangesTrieConfiguration::new(4, 2);
			let request = RemoteChangesRequest::<Header> {
				changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
					zero: (0, Default::default()),
					end: None,
					config: Some(config),
				}],
				first_block: (begin, begin_hash),
				last_block: (end, end_hash),
				max_block: (max, max_hash),
				tries_roots: (begin, begin_hash, local_roots_range),
				key: key.0,
				storage_key: None,
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
			b1, b4, b3, b4, None, &dave, 4
		).unwrap();

		// prepare local checker, having a root of changes trie CHT#0
		let local_cht_root = cht::compute_root::<Header, BlakeTwo256, _>(4, 0, remote_roots.iter().cloned().map(|ct| Ok(Some(ct)))).unwrap();
		let mut local_storage = DummyStorage::new();
		local_storage.changes_tries_cht_roots.insert(0, local_cht_root);
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(local_storage)),
			local_executor(),
		);

		// check proof on local client
		let config = ChangesTrieConfiguration::new(4, 2);
		let request = RemoteChangesRequest::<Header> {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(config),
			}],
			first_block: (1, b1),
			last_block: (4, b4),
			max_block: (4, b4),
			tries_roots: (3, b3, vec![remote_roots[2].clone(), remote_roots[3].clone()]),
			storage_key: None,
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
			local_executor(),
		);
		let local_checker = &local_checker as &dyn FetchChecker<Block>;
		let max = remote_client.chain_info().best_number;
		let max_hash = remote_client.chain_info().best_hash;

		let (begin, end, key, _) = test_cases[0].clone();
		let begin_hash = remote_client.block_hash(begin).unwrap().unwrap();
		let end_hash = remote_client.block_hash(end).unwrap().unwrap();

		// 'fetch' changes proof from remote node
		let key = StorageKey(key);
		let remote_proof = remote_client.key_changes_proof(
			begin_hash, end_hash, begin_hash, max_hash, None, &key).unwrap();

		let local_roots_range = local_roots.clone()[(begin - 1) as usize..].to_vec();
		let config = ChangesTrieConfiguration::new(4, 2);
		let request = RemoteChangesRequest::<Header> {
			changes_trie_configs: vec![sp_core::ChangesTrieConfigurationRange {
				zero: (0, Default::default()),
				end: None,
				config: Some(config),
			}],
			first_block: (begin, begin_hash),
			last_block: (end, end_hash),
			max_block: (max, max_hash),
			tries_roots: (begin, begin_hash, local_roots_range.clone()),
			storage_key: None,
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
			roots_proof: StorageProof::empty(),
		}).is_err());
		assert!(local_checker.check_changes_proof(&request, ChangesProof {
			max_block: remote_proof.max_block,
			proof: remote_proof.proof.clone(),
			roots: vec![(end + 1, Default::default())].into_iter().collect(),
			roots_proof: StorageProof::empty(),
		}).is_err());
	}

	#[test]
	fn check_changes_tries_proof_fails_if_proof_is_wrong() {
		// we're testing this test case here:
		// (1, 4, dave.clone(), vec![(4, 0), (1, 1), (1, 0)]),
		let (remote_client, remote_roots, _) = prepare_client_with_key_changes();
		let local_cht_root = cht::compute_root::<Header, BlakeTwo256, _>(
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
			b1, b4, b3, b4, None, &dave, 4
		).unwrap();

		// fails when changes trie CHT is missing from the local db
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			local_executor(),
		);
		assert!(local_checker.check_changes_tries_proof(4, &remote_proof.roots,
			remote_proof.roots_proof.clone()).is_err());

		// fails when proof is broken
		let mut local_storage = DummyStorage::new();
		local_storage.changes_tries_cht_roots.insert(0, local_cht_root);
		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(local_storage)),
			local_executor(),
		);
		let result = local_checker.check_changes_tries_proof(
			4, &remote_proof.roots, StorageProof::empty()
		);
		assert!(result.is_err());
	}

	#[test]
	fn check_body_proof_faulty() {
		let header = header_with_computed_extrinsics_root(
			vec![Extrinsic::IncludeData(vec![1, 2, 3, 4])]
		);
		let block = Block::new(header.clone(), Vec::new());

		let local_checker = TestChecker::new(
			Arc::new(DummyBlockchain::new(DummyStorage::new())),
			local_executor(),
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
			local_executor(),
		);

		let body_request = RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		};

		assert!(local_checker.check_body_proof(&body_request, block.extrinsics).is_ok());
	}
}
