// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::{sync::Arc, panic::UnwindSafe, result, cell::RefCell};
use codec::{Encode, Decode};
use sp_runtime::{
	generic::BlockId, traits::{Block as BlockT, HashFor, NumberFor},
};
use sp_state_machine::{
	self, OverlayedChanges, Ext, ExecutionManager, StateMachine, ExecutionStrategy,
	backend::Backend as _, StorageProof,
};
use sc_executor::{RuntimeVersion, RuntimeInfo, NativeVersion};
use sp_externalities::Extensions;
use sp_core::{
	NativeOrEncoded, NeverNativeValue, traits::{CodeExecutor, SpawnNamed, RuntimeCode},
	offchain::storage::OffchainOverlayedChanges,
};
use sp_api::{ProofRecorder, InitializeBlock, StorageTransactionCache};
use sc_client_api::{backend, call_executor::CallExecutor};
use super::{client::ClientConfig, wasm_override::WasmOverride};

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
	wasm_override: Option<WasmOverride<E>>,
	spawn_handle: Box<dyn SpawnNamed>,
	client_config: ClientConfig,
}

impl<B, E> LocalCallExecutor<B, E>
where
	E: CodeExecutor + RuntimeInfo + Clone + 'static
{
	/// Creates new instance of local call executor.
	pub fn new(
		backend: Arc<B>,
		executor: E,
		spawn_handle: Box<dyn SpawnNamed>,
		client_config: ClientConfig,
	) -> sp_blockchain::Result<Self> {
		let wasm_override = client_config.wasm_runtime_overrides
			.as_ref()
			.map(|p| WasmOverride::new(p.clone(), executor.clone()))
			.transpose()?;

		Ok(LocalCallExecutor {
			backend,
			executor,
			wasm_override,
			spawn_handle,
			client_config,
		})
	}

	/// Check if local runtime code overrides are enabled and one is available
	/// for the given `BlockId`. If yes, return it; otherwise return the same
	/// `RuntimeCode` instance that was passed.
	fn check_override<'a, Block>(
		&'a self,
		onchain_code: RuntimeCode<'a>,
		id: &BlockId<Block>,
	) -> sp_blockchain::Result<RuntimeCode<'a>>
	where
		Block: BlockT,
		B: backend::Backend<Block>,
	{
		let code = self.wasm_override
			.as_ref()
			.map::<sp_blockchain::Result<Option<RuntimeCode>>, _>(|o| {
				let spec = self.runtime_version(id)?.spec_version;
				Ok(o.get(&spec, onchain_code.heap_pages))
			})
			.transpose()?
			.flatten()
			.unwrap_or(onchain_code);

		Ok(code)
	}
}

impl<B, E> Clone for LocalCallExecutor<B, E> where E: Clone {
	fn clone(&self) -> Self {
		LocalCallExecutor {
			backend: self.backend.clone(),
			executor: self.executor.clone(),
			wasm_override: self.wasm_override.clone(),
			spawn_handle: self.spawn_handle.clone(),
			client_config: self.client_config.clone(),
		}
	}
}

impl<B, E, Block> CallExecutor<Block> for LocalCallExecutor<B, E>
where
	B: backend::Backend<Block>,
	E: CodeExecutor + RuntimeInfo + Clone + 'static,
	Block: BlockT,
{
	type Error = E::Error;

	type Backend = B;

	fn call(
		&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		extensions: Option<Extensions>,
	) -> sp_blockchain::Result<Vec<u8>> {
		let mut changes = OverlayedChanges::default();
		let mut offchain_changes = if self.client_config.offchain_indexing_api {
			OffchainOverlayedChanges::enabled()
		} else {
			OffchainOverlayedChanges::disabled()
		};
		let changes_trie = backend::changes_tries_state_at_block(
			id, self.backend.changes_trie_storage()
		)?;
		let state = self.backend.state_at(*id)?;
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);
		let runtime_code = state_runtime_code.runtime_code()
			.map_err(sp_blockchain::Error::RuntimeCode)?;
		let runtime_code = self.check_override(runtime_code, id)?;

		let return_data = StateMachine::new(
			&state,
			changes_trie,
			&mut changes,
			&mut offchain_changes,
			&self.executor,
			method,
			call_data,
			extensions.unwrap_or_default(),
			&runtime_code,
			self.spawn_handle.clone(),
		).execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			strategy.get_manager(),
			None,
		)?;

		Ok(return_data.into_encoded())
	}

	fn contextual_call<
		'a,
		IB: Fn() -> sp_blockchain::Result<()>,
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
		offchain_changes: &RefCell<OffchainOverlayedChanges>,
		storage_transaction_cache: Option<&RefCell<
			StorageTransactionCache<Block, B::State>
		>>,
		initialize_block: InitializeBlock<'a, Block>,
		execution_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		recorder: &Option<ProofRecorder<Block>>,
		extensions: Option<Extensions>,
	) -> Result<NativeOrEncoded<R>, sp_blockchain::Error> where ExecutionManager<EM>: Clone {
		match initialize_block {
			InitializeBlock::Do(ref init_block)
				if init_block.borrow().as_ref().map(|id| id != at).unwrap_or(true) => {
				initialize_block_fn()?;
			},
			// We don't need to initialize the runtime at a block.
			_ => {},
		}

		let changes_trie_state = backend::changes_tries_state_at_block(at, self.backend.changes_trie_storage())?;
		let mut storage_transaction_cache = storage_transaction_cache.map(|c| c.borrow_mut());

		let mut state = self.backend.state_at(*at)?;

		let changes = &mut *changes.borrow_mut();
		let offchain_changes = &mut *offchain_changes.borrow_mut();

		match recorder {
			Some(recorder) => {
				let trie_state = state.as_trie_backend()
					.ok_or_else(||
						Box::new(sp_state_machine::ExecutionError::UnableToGenerateProof) as Box<dyn sp_state_machine::Error>
					)?;

				let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&trie_state);
				// It is important to extract the runtime code here before we create the proof
				// recorder.
				
				let runtime_code = state_runtime_code.runtime_code()
					.map_err(sp_blockchain::Error::RuntimeCode)?;
				let runtime_code = self.check_override(runtime_code, at)?;

				let backend = sp_state_machine::ProvingBackend::new_with_recorder(
					trie_state,
					recorder.clone(),
				);

				let mut state_machine = StateMachine::new(
					&backend,
					changes_trie_state,
					changes,
					offchain_changes,
					&self.executor,
					method,
					call_data,
					extensions.unwrap_or_default(),
					&runtime_code,
					self.spawn_handle.clone(),
				);
				// TODO: https://github.com/paritytech/substrate/issues/4455
				// .with_storage_transaction_cache(storage_transaction_cache.as_mut().map(|c| &mut **c))
				state_machine.execute_using_consensus_failure_handler(execution_manager, native_call)
			},
			None => {
				let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);
				let runtime_code = state_runtime_code.runtime_code()
					.map_err(sp_blockchain::Error::RuntimeCode)?;
				let runtime_code = self.check_override(runtime_code, at)?;

				let mut state_machine = StateMachine::new(
					&state,
					changes_trie_state,
					changes,
					offchain_changes,
					&self.executor,
					method,
					call_data,
					extensions.unwrap_or_default(),
					&runtime_code,
					self.spawn_handle.clone(),
				).with_storage_transaction_cache(storage_transaction_cache.as_mut().map(|c| &mut **c));
				state_machine.execute_using_consensus_failure_handler(execution_manager, native_call)
			}
		}.map_err(Into::into)
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> sp_blockchain::Result<RuntimeVersion> {
		let mut overlay = OverlayedChanges::default();
		let mut offchain_overlay = OffchainOverlayedChanges::default();
		let changes_trie_state = backend::changes_tries_state_at_block(
			id,
			self.backend.changes_trie_storage(),
		)?;
		let state = self.backend.state_at(*id)?;
		let mut cache = StorageTransactionCache::<Block, B::State>::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut offchain_overlay,
			&mut cache,
			&state,
			changes_trie_state,
			None,
		);
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);
		let runtime_code = state_runtime_code.runtime_code()
			.map_err(sp_blockchain::Error::RuntimeCode)?;
		self.executor.runtime_version(&mut ext, &runtime_code)
			.map_err(|e| sp_blockchain::Error::VersionInvalid(format!("{:?}", e)).into())
	}

	fn prove_at_trie_state<S: sp_state_machine::TrieBackendStorage<HashFor<Block>>>(
		&self,
		trie_state: &sp_state_machine::TrieBackend<S, HashFor<Block>>,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, StorageProof), sp_blockchain::Error> {
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(trie_state);
		let runtime_code = state_runtime_code.runtime_code()
			.map_err(sp_blockchain::Error::RuntimeCode)?;
		sp_state_machine::prove_execution_on_trie_backend::<_, _, NumberFor<Block>, _, _>(
			trie_state,
			overlay,
			&self.executor,
			self.spawn_handle.clone(),
			method,
			call_data,
			&runtime_code,
		)
		.map_err(Into::into)
	}

	fn native_runtime_version(&self) -> Option<&NativeVersion> {
		Some(self.executor.native_version())
	}
}

impl<B, E, Block> sp_version::GetRuntimeVersion<Block> for LocalCallExecutor<B, E>
	where
		B: backend::Backend<Block>,
		E: CodeExecutor + RuntimeInfo + Clone + 'static,
		Block: BlockT,
{
	fn native_version(&self) -> &sp_version::NativeVersion {
		self.executor.native_version()
	}

	fn runtime_version(
		&self,
		at: &BlockId<Block>,
	) -> Result<sp_version::RuntimeVersion, String> {
		CallExecutor::runtime_version(self, at).map_err(|e| format!("{:?}", e))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_test_runtime_client::{LocalExecutor, GenesisInit, runtime};
	use sc_executor::{NativeExecutor, WasmExecutionMethod};
	use sp_core::{traits::{WrappedRuntimeCode, FetchRuntimeCode}, testing::TaskExecutor};
	use sc_client_api::in_mem;

	#[test]
	fn should_get_override_if_exists() {
		let executor =
			NativeExecutor::<LocalExecutor>::new(WasmExecutionMethod::Interpreted, Some(128), 1);

		let overrides = crate::client::wasm_override::dummy_overrides(&executor);
		let onchain_code = WrappedRuntimeCode(substrate_test_runtime::wasm_binary_unwrap().into());
		let onchain_code = RuntimeCode {
			code_fetcher: &onchain_code,
			heap_pages: Some(128),
			hash: vec![0, 0, 0, 0],
		};

		let backend = Arc::new(in_mem::Backend::<runtime::Block>::new());

		// wasm_runtime_overrides is `None` here because we construct the
		// LocalCallExecutor directly later on
		let client_config = ClientConfig {
			offchain_worker_enabled: false,
			offchain_indexing_api: false,
			wasm_runtime_overrides: None,
		};

		// client is used for the convenience of creating and inserting the genesis block.
		let _client = substrate_test_runtime_client::client::new_with_backend::<
			_,
			_,
			runtime::Block,
			_,
			runtime::RuntimeApi,
		>(
			backend.clone(),
			executor.clone(),
			&substrate_test_runtime_client::GenesisParameters::default().genesis_storage(),
			None,
			Box::new(TaskExecutor::new()),
			None,
			Default::default(),
		).expect("Creates a client");

		let call_executor = LocalCallExecutor {
			backend: backend.clone(),
			executor,
			wasm_override: Some(overrides),
			spawn_handle: Box::new(TaskExecutor::new()),
			client_config,
		};

		let check = call_executor.check_override(onchain_code, &BlockId::Number(Default::default()))
			.expect("RuntimeCode override");

		assert_eq!(Some(vec![2, 2, 2, 2, 2, 2, 2, 2]), check.fetch_runtime_code().map(Into::into));
	}
}
