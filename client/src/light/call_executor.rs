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

//! Methods that light client could use to execute runtime calls.

use std::{
	sync::Arc, panic::UnwindSafe, result, cell::RefCell,
};

use codec::{Encode, Decode};
use sp_core::{convert_hash, NativeOrEncoded, traits::CodeExecutor};
use sp_runtime::{
	generic::BlockId, traits::{One, Block as BlockT, Header as HeaderT, HasherFor},
};
use sp_externalities::Extensions;
use sp_state_machine::{
	self, Backend as StateBackend, OverlayedChanges, ExecutionStrategy, create_proof_check_backend,
	execution_proof_check_on_trie_backend, ExecutionManager, StorageProof,
};
use hash_db::Hasher;

use sp_api::{ProofRecorder, InitializeBlock, StorageTransactionCache};

use sp_blockchain::{Error as ClientError, Result as ClientResult};

use sc_client_api::{
	backend::RemoteBackend,
	light::RemoteCallRequest,
	call_executor::CallExecutor
};
use sc_executor::{RuntimeVersion, NativeVersion};

/// Call executor that is able to execute calls only on genesis state.
///
/// Trying to execute call on non-genesis state leads to error.
pub struct GenesisCallExecutor<B, L> {
	backend: Arc<B>,
	local: L,
}

impl<B, L> GenesisCallExecutor<B, L> {
	/// Create new genesis call executor.
	pub fn new(backend: Arc<B>, local: L) -> Self {
		Self { backend, local }
	}
}

impl<B, L: Clone> Clone for GenesisCallExecutor<B, L> {
	fn clone(&self) -> Self {
		GenesisCallExecutor {
			backend: self.backend.clone(),
			local: self.local.clone(),
		}
	}
}

impl<Block, B, Local> CallExecutor<Block> for
	GenesisCallExecutor<B, Local>
	where
		Block: BlockT,
		B: RemoteBackend<Block>,
		Local: CallExecutor<Block>,
{
	type Error = ClientError;

	type Backend = B;

	fn call(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		extensions: Option<Extensions>,
	) -> ClientResult<Vec<u8>> {
		match self.backend.is_local_state_available(id) {
			true => self.local.call(id, method, call_data, strategy, extensions),
			false => Err(ClientError::NotAvailableOnLightClient),
		}
	}

	fn contextual_call<
		'a,
		IB: Fn() -> ClientResult<()>,
		EM: Fn(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(
		&self,
		initialize_block_fn: IB,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		_: Option<&RefCell<StorageTransactionCache<Block, B::State>>>,
		initialize_block: InitializeBlock<'a, Block>,
		_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		recorder: &Option<ProofRecorder<Block>>,
		extensions: Option<Extensions>,
	) -> ClientResult<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone {
		// there's no actual way/need to specify native/wasm execution strategy on light node
		// => we can safely ignore passed values

		match self.backend.is_local_state_available(at) {
			true => CallExecutor::contextual_call::<
				_,
				fn(
					Result<NativeOrEncoded<R>, Local::Error>,
					Result<NativeOrEncoded<R>, Local::Error>,
				) -> Result<NativeOrEncoded<R>, Local::Error>,
				_,
				NC
			>(
				&self.local,
				initialize_block_fn,
				at,
				method,
				call_data,
				changes,
				None,
				initialize_block,
				ExecutionManager::NativeWhenPossible,
				native_call,
				recorder,
				extensions,
			).map_err(|e| ClientError::Execution(Box::new(e.to_string()))),
			false => Err(ClientError::NotAvailableOnLightClient),
		}
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> ClientResult<RuntimeVersion> {
		match self.backend.is_local_state_available(id) {
			true => self.local.runtime_version(id),
			false => Err(ClientError::NotAvailableOnLightClient),
		}
	}

	fn prove_at_trie_state<S: sp_state_machine::TrieBackendStorage<HasherFor<Block>>>(
		&self,
		_state: &sp_state_machine::TrieBackend<S, HasherFor<Block>>,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8],
	) -> ClientResult<(Vec<u8>, StorageProof)> {
		Err(ClientError::NotAvailableOnLightClient)
	}

	fn native_runtime_version(&self) -> Option<&NativeVersion> {
		None
	}
}

/// Prove contextual execution using given block header in environment.
///
/// Method is executed using passed header as environment' current block.
/// Proof includes both environment preparation proof and method execution proof.
pub fn prove_execution<Block, S, E>(
	mut state: S,
	header: Block::Header,
	executor: &E,
	method: &str,
	call_data: &[u8],
) -> ClientResult<(Vec<u8>, StorageProof)>
	where
		Block: BlockT,
		S: StateBackend<HasherFor<Block>>,
		E: CallExecutor<Block>,
{
	let trie_state = state.as_trie_backend()
		.ok_or_else(||
			Box::new(sp_state_machine::ExecutionError::UnableToGenerateProof) as
				Box<dyn sp_state_machine::Error>
		)?;

	// prepare execution environment + record preparation proof
	let mut changes = Default::default();
	let (_, init_proof) = executor.prove_at_trie_state(
		trie_state,
		&mut changes,
		"Core_initialize_block",
		&header.encode(),
	)?;

	// execute method + record execution proof
	let (result, exec_proof) = executor.prove_at_trie_state(
		&trie_state,
		&mut changes,
		method,
		call_data,
	)?;
	let total_proof = StorageProof::merge(vec![init_proof, exec_proof]);

	Ok((result, total_proof))
}

/// Check remote contextual execution proof using given backend.
///
/// Method is executed using passed header as environment' current block.
/// Proof should include both environment preparation proof and method execution proof.
pub fn check_execution_proof<Header, E, H>(
	executor: &E,
	request: &RemoteCallRequest<Header>,
	remote_proof: StorageProof,
) -> ClientResult<Vec<u8>>
	where
		Header: HeaderT,
		E: CodeExecutor + Clone + 'static,
		H: Hasher,
		H::Out: Ord + codec::Codec + 'static,
{
	check_execution_proof_with_make_header::<Header, E, H, _>(
		executor,
		request,
		remote_proof,
		|header| <Header as HeaderT>::new(
			*header.number() + One::one(),
			Default::default(),
			Default::default(),
			header.hash(),
			Default::default(),
		),
	)
}

fn check_execution_proof_with_make_header<Header, E, H, MakeNextHeader: Fn(&Header) -> Header>(
	executor: &E,
	request: &RemoteCallRequest<Header>,
	remote_proof: StorageProof,
	make_next_header: MakeNextHeader,
) -> ClientResult<Vec<u8>>
	where
		Header: HeaderT,
		E: CodeExecutor + Clone + 'static,
		H: Hasher,
		H::Out: Ord + codec::Codec + 'static,
{
	let local_state_root = request.header.state_root();
	let root: H::Out = convert_hash(&local_state_root);

	// prepare execution environment + check preparation proof
	let mut changes = OverlayedChanges::default();
	let trie_backend = create_proof_check_backend(root, remote_proof)?;
	let next_header = make_next_header(&request.header);

	// TODO: Remove when solved: https://github.com/paritytech/substrate/issues/5047
	let runtime_code = sp_state_machine::backend::get_runtime_code(&trie_backend)?;

	execution_proof_check_on_trie_backend::<H, Header::Number, _>(
		&trie_backend,
		&mut changes,
		executor,
		"Core_initialize_block",
		&next_header.encode(),
		&runtime_code,
	)?;

	// execute method
	execution_proof_check_on_trie_backend::<H, Header::Number, _>(
		&trie_backend,
		&mut changes,
		executor,
		&request.method,
		&request.call_data,
		&runtime_code,
	)
	.map_err(Into::into)
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_consensus::BlockOrigin;
	use substrate_test_runtime_client::{
		runtime::{Header, Digest, Block}, TestClient, ClientBlockImportExt,
	};
	use sc_executor::{NativeExecutor, WasmExecutionMethod};
	use sp_core::{Blake2Hasher, H256};
	use sc_client_api::backend::{Backend, NewBlockState};
	use crate::in_mem::Backend as InMemBackend;

	struct DummyCallExecutor;

	impl CallExecutor<Block> for DummyCallExecutor {
		type Error = ClientError;

		type Backend = substrate_test_runtime_client::Backend;

		fn call(
			&self,
			_id: &BlockId<Block>,
			_method: &str,
			_call_data: &[u8],
			_strategy: ExecutionStrategy,
			_extensions: Option<Extensions>,
		) -> Result<Vec<u8>, ClientError> {
			Ok(vec![42])
		}

		fn contextual_call<
			'a,
			IB: Fn() -> ClientResult<()>,
			EM: Fn(
				Result<NativeOrEncoded<R>, Self::Error>,
				Result<NativeOrEncoded<R>, Self::Error>
			) -> Result<NativeOrEncoded<R>, Self::Error>,
			R: Encode + Decode + PartialEq,
			NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		>(
			&self,
			_initialize_block_fn: IB,
			_at: &BlockId<Block>,
			_method: &str,
			_call_data: &[u8],
			_changes: &RefCell<OverlayedChanges>,
			_storage_transaction_cache: Option<&RefCell<
				StorageTransactionCache<
					Block,
					<Self::Backend as sc_client_api::backend::Backend<Block>>::State,
				>
			>>,
			_initialize_block: InitializeBlock<'a, Block>,
			_execution_manager: ExecutionManager<EM>,
			_native_call: Option<NC>,
			_proof_recorder: &Option<ProofRecorder<Block>>,
			_extensions: Option<Extensions>,
		) -> ClientResult<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone {
			unreachable!()
		}

		fn runtime_version(&self, _id: &BlockId<Block>) -> Result<RuntimeVersion, ClientError> {
			unreachable!()
		}

		fn prove_at_trie_state<S: sp_state_machine::TrieBackendStorage<HasherFor<Block>>>(
			&self,
			_trie_state: &sp_state_machine::TrieBackend<S, HasherFor<Block>>,
			_overlay: &mut OverlayedChanges,
			_method: &str,
			_call_data: &[u8]
		) -> Result<(Vec<u8>, StorageProof), ClientError> {
			unreachable!()
		}

		fn native_runtime_version(&self) -> Option<&NativeVersion> {
			unreachable!()
		}
	}

	fn local_executor() -> NativeExecutor<substrate_test_runtime_client::LocalExecutor> {
		NativeExecutor::new(WasmExecutionMethod::Interpreted, None)
	}

	#[test]
	fn execution_proof_is_generated_and_checked() {
		fn execute(remote_client: &TestClient, at: u64, method: &'static str) -> (Vec<u8>, Vec<u8>) {
			let remote_block_id = BlockId::Number(at);
			let remote_header = remote_client.header(&remote_block_id).unwrap().unwrap();

			// 'fetch' execution proof from remote node
			let (remote_result, remote_execution_proof) = remote_client.execution_proof(
				&remote_block_id,
				method,
				&[]
			).unwrap();

			// check remote execution proof locally
			let local_result = check_execution_proof::<_, _, Blake2Hasher>(
				&local_executor(),
				&RemoteCallRequest {
					block: substrate_test_runtime_client::runtime::Hash::default(),
					header: remote_header,
					method: method.into(),
					call_data: vec![],
					retry_count: None,
				},
				remote_execution_proof,
			).unwrap();

			(remote_result, local_result)
		}

		fn execute_with_proof_failure(remote_client: &TestClient, at: u64, method: &'static str) {
			let remote_block_id = BlockId::Number(at);
			let remote_header = remote_client.header(&remote_block_id).unwrap().unwrap();

			// 'fetch' execution proof from remote node
			let (_, remote_execution_proof) = remote_client.execution_proof(
				&remote_block_id,
				method,
				&[]
			).unwrap();

			// check remote execution proof locally
			let execution_result = check_execution_proof_with_make_header::<_, _, Blake2Hasher, _>(
				&local_executor(),
				&RemoteCallRequest {
					block: substrate_test_runtime_client::runtime::Hash::default(),
					header: remote_header,
					method: method.into(),
					call_data: vec![],
					retry_count: None,
				},
				remote_execution_proof,
				|header| <Header as HeaderT>::new(
					at + 1,
					Default::default(),
					Default::default(),
					header.hash(),
					header.digest().clone(), // this makes next header wrong
				),
			);
			match execution_result {
				Err(sp_blockchain::Error::Execution(_)) => (),
				_ => panic!("Unexpected execution result: {:?}", execution_result),
			}
		}

		// prepare remote client
		let mut remote_client = substrate_test_runtime_client::new();
		for i in 1u32..3u32 {
			let mut digest = Digest::default();
			digest.push(sp_runtime::generic::DigestItem::Other::<H256>(i.to_le_bytes().to_vec()));
			remote_client.import_justified(
				BlockOrigin::Own,
				remote_client.new_block(digest).unwrap().build().unwrap().block,
				Default::default(),
			).unwrap();
		}

		// check method that doesn't requires environment
		let (remote, local) = execute(&remote_client, 0, "Core_version");
		assert_eq!(remote, local);

		let (remote, local) = execute(&remote_client, 2, "Core_version");
		assert_eq!(remote, local);

		// check method that requires environment
		let (_, block) = execute(&remote_client, 0, "BlockBuilder_finalize_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 1);

		let (_, block) = execute(&remote_client, 2, "BlockBuilder_finalize_block");
		let local_block: Header = Decode::decode(&mut &block[..]).unwrap();
		assert_eq!(local_block.number, 3);

		// check that proof check doesn't panic even if proof is incorrect AND no panic handler is set
		execute_with_proof_failure(&remote_client, 2, "Core_version");

		// check that proof check doesn't panic even if proof is incorrect AND panic handler is set
		sp_panic_handler::set("TEST", "1.2.3");
		execute_with_proof_failure(&remote_client, 2, "Core_version");
	}

	#[test]
	fn code_is_executed_at_genesis_only() {
		let backend = Arc::new(InMemBackend::<Block>::new());
		let def = H256::default();
		let header0 = substrate_test_runtime_client::runtime::Header::new(0, def, def, def, Default::default());
		let hash0 = header0.hash();
		let header1 = substrate_test_runtime_client::runtime::Header::new(1, def, def, hash0, Default::default());
		let hash1 = header1.hash();
		backend.blockchain().insert(hash0, header0, None, None, NewBlockState::Final).unwrap();
		backend.blockchain().insert(hash1, header1, None, None, NewBlockState::Final).unwrap();

		let genesis_executor = GenesisCallExecutor::new(backend, DummyCallExecutor);
		assert_eq!(
			genesis_executor.call(
				&BlockId::Number(0),
				"test_method",
				&[],
				ExecutionStrategy::NativeElseWasm,
				None,
			).unwrap(),
			vec![42],
		);

		let call_on_unavailable = genesis_executor.call(
			&BlockId::Number(1),
			"test_method",
			&[],
			ExecutionStrategy::NativeElseWasm,
			None,
		);

		match call_on_unavailable {
			Err(ClientError::NotAvailableOnLightClient) => (),
			_ => unreachable!("unexpected result: {:?}", call_on_unavailable),
		}
	}
}
