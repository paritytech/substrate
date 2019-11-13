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

//! Methods that light client could use to execute runtime calls.

use std::{
	sync::Arc, panic::UnwindSafe, result, cell::RefCell,
};

use codec::{Encode, Decode};
use primitives::{
	offchain::OffchainExt, H256, Blake2Hasher, convert_hash, NativeOrEncoded,
	traits::CodeExecutor,
};
use sr_primitives::{
	generic::BlockId, traits::{One, Block as BlockT, Header as HeaderT, NumberFor},
};
use state_machine::{
	self, Backend as StateBackend, OverlayedChanges, ExecutionStrategy, create_proof_check_backend,
	execution_proof_check_on_trie_backend, ExecutionManager, ChangesTrieTransaction, StorageProof,
	merge_storage_proofs,
};
use hash_db::Hasher;

use sr_api::{ProofRecorder, InitializeBlock};

use crate::backend::RemoteBackend;
use crate::call_executor::CallExecutor;
use crate::error::{Error as ClientError, Result as ClientResult};
use crate::light::fetcher::RemoteCallRequest;
use executor::{RuntimeVersion, NativeVersion};

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

impl<Block, B, Local> CallExecutor<Block, Blake2Hasher> for
	GenesisCallExecutor<B, Local>
	where
		Block: BlockT<Hash=H256>,
		B: RemoteBackend<Block, Blake2Hasher>,
		Local: CallExecutor<Block, Blake2Hasher>,
{
	type Error = ClientError;

	fn call(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		side_effects_handler: Option<OffchainExt>,
	) -> ClientResult<Vec<u8>> {
		match self.backend.is_local_state_available(id) {
			true => self.local.call(id, method, call_data, strategy, side_effects_handler),
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
		initialize_block: InitializeBlock<'a, Block>,
		_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		side_effects_handler: Option<OffchainExt>,
		recorder: &Option<ProofRecorder<Block>>,
		enable_keystore: bool,
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
				initialize_block,
				ExecutionManager::NativeWhenPossible,
				native_call,
				side_effects_handler,
				recorder,
				enable_keystore,
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

	fn call_at_state<
		S: StateBackend<Blake2Hasher>,
		FF: FnOnce(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(&self,
		_state: &S,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8],
		_manager: ExecutionManager<FF>,
		_native_call: Option<NC>,
		_side_effects_handler: Option<OffchainExt>,
	) -> ClientResult<(
		NativeOrEncoded<R>,
		(S::Transaction, <Blake2Hasher as Hasher>::Out),
		Option<ChangesTrieTransaction<Blake2Hasher, NumberFor<Block>>>,
	)> {
		Err(ClientError::NotAvailableOnLightClient)
	}

	fn prove_at_trie_state<S: state_machine::TrieBackendStorage<Blake2Hasher>>(
		&self,
		_state: &state_machine::TrieBackend<S, Blake2Hasher>,
		_changes: &mut OverlayedChanges,
		_method: &str,
		_call_data: &[u8]
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
		Block: BlockT<Hash=H256>,
		S: StateBackend<Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
{
	let trie_state = state.as_trie_backend()
		.ok_or_else(|| Box::new(state_machine::ExecutionError::UnableToGenerateProof) as Box<dyn state_machine::Error>)?;

	// prepare execution environment + record preparation proof
	let mut changes = Default::default();
	let (_, init_proof) = executor.prove_at_trie_state(
		trie_state,
		&mut changes,
		"Core_initialize_block",
		&header.encode(),
	)?;

	// execute method + record execution proof
	let (result, exec_proof) = executor.prove_at_trie_state(&trie_state, &mut changes, method, call_data)?;
	let total_proof = merge_storage_proofs(vec![init_proof, exec_proof]);

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
		E: CodeExecutor,
		H: Hasher<Out=H256>,
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
		E: CodeExecutor,
		H: Hasher<Out=H256>,
{
	let local_state_root = request.header.state_root();
	let root: H::Out = convert_hash(&local_state_root);

	// prepare execution environment + check preparation proof
	let mut changes = OverlayedChanges::default();
	let trie_backend = create_proof_check_backend(root, remote_proof)?;
	let next_header = make_next_header(&request.header);
	execution_proof_check_on_trie_backend::<H, _>(
		&trie_backend,
		&mut changes,
		executor,
		"Core_initialize_block",
		&next_header.encode(),
		None,
	)?;

	// execute method
	execution_proof_check_on_trie_backend::<H, _>(
		&trie_backend,
		&mut changes,
		executor,
		&request.method,
		&request.call_data,
		None,
	).map_err(Into::into)
}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus::BlockOrigin;
	use test_client::{self, runtime::{Header, Digest, Block}, ClientExt, TestClient};
	use executor::{NativeExecutor, WasmExecutionMethod};
	use primitives::Blake2Hasher;
	use crate::backend::{Backend, NewBlockState};
	use crate::in_mem::Backend as InMemBackend;

	struct DummyCallExecutor;

	impl CallExecutor<Block, Blake2Hasher> for DummyCallExecutor {
		type Error = ClientError;

		fn call(
			&self,
			_id: &BlockId<Block>,
			_method: &str,
			_call_data: &[u8],
			_strategy: ExecutionStrategy,
			_side_effects_handler: Option<OffchainExt>,
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
			_initialize_block: InitializeBlock<'a, Block>,
			_execution_manager: ExecutionManager<EM>,
			_native_call: Option<NC>,
			_side_effects_handler: Option<OffchainExt>,
			_proof_recorder: &Option<ProofRecorder<Block>>,
			_enable_keystore: bool,
		) -> ClientResult<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone {
			unreachable!()
		}

		fn runtime_version(&self, _id: &BlockId<Block>) -> Result<RuntimeVersion, ClientError> {
			unreachable!()
		}

		fn call_at_state<
			S: state_machine::Backend<Blake2Hasher>,
			F: FnOnce(
				Result<NativeOrEncoded<R>, Self::Error>,
				Result<NativeOrEncoded<R>, Self::Error>
			) -> Result<NativeOrEncoded<R>, Self::Error>,
			R: Encode + Decode + PartialEq,
			NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		>(&self,
			_state: &S,
			_overlay: &mut OverlayedChanges,
			_method: &str,
			_call_data: &[u8],
			_manager: ExecutionManager<F>,
			_native_call: Option<NC>,
			_side_effects_handler: Option<OffchainExt>,
		) -> Result<
			(
				NativeOrEncoded<R>,
				(S::Transaction, H256),
				Option<ChangesTrieTransaction<Blake2Hasher, NumberFor<Block>>>,
			),
			ClientError,
		> {
			unreachable!()
		}

		fn prove_at_trie_state<S: state_machine::TrieBackendStorage<Blake2Hasher>>(
			&self,
			_trie_state: &state_machine::TrieBackend<S, Blake2Hasher>,
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

	fn local_executor() -> NativeExecutor<test_client::LocalExecutor> {
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
					block: test_client::runtime::Hash::default(),
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
					block: test_client::runtime::Hash::default(),
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
				Err(crate::error::Error::Execution(_)) => (),
				_ => panic!("Unexpected execution result: {:?}", execution_result),
			}
		}

		// prepare remote client
		let remote_client = test_client::new();
		for i in 1u32..3u32 {
			let mut digest = Digest::default();
			digest.push(sr_primitives::generic::DigestItem::Other::<H256>(i.to_le_bytes().to_vec()));
			remote_client.import_justified(
				BlockOrigin::Own,
				remote_client.new_block(digest).unwrap().bake().unwrap(),
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
		panic_handler::set("TEST", "1.2.3");
		execute_with_proof_failure(&remote_client, 2, "Core_version");
	}

	#[test]
	fn code_is_executed_at_genesis_only() {
		let backend = Arc::new(InMemBackend::<Block, Blake2Hasher>::new());
		let def = H256::default();
		let header0 = test_client::runtime::Header::new(0, def, def, def, Default::default());
		let hash0 = header0.hash();
		let header1 = test_client::runtime::Header::new(1, def, def, hash0, Default::default());
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
