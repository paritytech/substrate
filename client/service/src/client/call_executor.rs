// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use super::{client::ClientConfig, wasm_override::WasmOverride, wasm_substitutes::WasmSubstitutes};
use codec::{Decode, Encode};
use sc_client_api::{backend, call_executor::CallExecutor, HeaderBackend};
use sc_executor::{RuntimeVersion, RuntimeVersionOf};
use sp_api::{ProofRecorder, StorageTransactionCache};
use sp_core::{
	traits::{CodeExecutor, RuntimeCode, SpawnNamed},
	NativeOrEncoded, NeverNativeValue,
};
use sp_externalities::Extensions;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use sp_state_machine::{
	backend::AsTrieBackend, ExecutionManager, ExecutionStrategy, Ext, OverlayedChanges,
	StateMachine, StorageProof,
};
use std::{cell::RefCell, panic::UnwindSafe, result, sync::Arc};

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<Block: BlockT, B, E> {
	backend: Arc<B>,
	executor: E,
	wasm_override: Arc<Option<WasmOverride>>,
	wasm_substitutes: WasmSubstitutes<Block, E, B>,
	spawn_handle: Box<dyn SpawnNamed>,
	client_config: ClientConfig<Block>,
}

impl<Block: BlockT, B, E> LocalCallExecutor<Block, B, E>
where
	E: CodeExecutor + RuntimeVersionOf + Clone + 'static,
	B: backend::Backend<Block>,
{
	/// Creates new instance of local call executor.
	pub fn new(
		backend: Arc<B>,
		executor: E,
		spawn_handle: Box<dyn SpawnNamed>,
		client_config: ClientConfig<Block>,
	) -> sp_blockchain::Result<Self> {
		let wasm_override = client_config
			.wasm_runtime_overrides
			.as_ref()
			.map(|p| WasmOverride::new(p.clone(), &executor))
			.transpose()?;

		let wasm_substitutes = WasmSubstitutes::new(
			client_config.wasm_runtime_substitutes.clone(),
			executor.clone(),
			backend.clone(),
		)?;

		Ok(LocalCallExecutor {
			backend,
			executor,
			wasm_override: Arc::new(wasm_override),
			spawn_handle,
			client_config,
			wasm_substitutes,
		})
	}

	/// Check if local runtime code overrides are enabled and one is available
	/// for the given `BlockId`. If yes, return it; otherwise return the same
	/// `RuntimeCode` instance that was passed.
	fn check_override<'a>(
		&'a self,
		onchain_code: RuntimeCode<'a>,
		id: &BlockId<Block>,
	) -> sp_blockchain::Result<RuntimeCode<'a>>
	where
		Block: BlockT,
		B: backend::Backend<Block>,
	{
		let spec = CallExecutor::runtime_version(self, id)?;
		let code =
			if let Some(d) =
				self.wasm_override.as_ref().as_ref().and_then(|o| {
					o.get(&spec.spec_version, onchain_code.heap_pages, &spec.spec_name)
				}) {
				log::debug!(target: "wasm_overrides", "using WASM override for block {}", id);
				d
			} else if let Some(s) =
				self.wasm_substitutes.get(spec.spec_version, onchain_code.heap_pages, id)
			{
				log::debug!(target: "wasm_substitutes", "Using WASM substitute for block {:?}", id);
				s
			} else {
				log::debug!(
					target: "wasm_overrides",
					"No WASM override available for block {}, using onchain code",
					id
				);
				onchain_code
			};

		Ok(code)
	}
}

impl<Block: BlockT, B, E> Clone for LocalCallExecutor<Block, B, E>
where
	E: Clone,
{
	fn clone(&self) -> Self {
		LocalCallExecutor {
			backend: self.backend.clone(),
			executor: self.executor.clone(),
			wasm_override: self.wasm_override.clone(),
			spawn_handle: self.spawn_handle.clone(),
			client_config: self.client_config.clone(),
			wasm_substitutes: self.wasm_substitutes.clone(),
		}
	}
}

impl<B, E, Block> CallExecutor<Block> for LocalCallExecutor<Block, B, E>
where
	B: backend::Backend<Block>,
	E: CodeExecutor + RuntimeVersionOf + Clone + 'static,
	Block: BlockT,
{
	type Error = E::Error;

	type Backend = B;

	fn call(
		&self,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		extensions: Option<Extensions>,
	) -> sp_blockchain::Result<Vec<u8>> {
		let mut changes = OverlayedChanges::default();
		let state = self.backend.state_at(*at)?;
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);
		let runtime_code =
			state_runtime_code.runtime_code().map_err(sp_blockchain::Error::RuntimeCode)?;

		let runtime_code = self.check_override(runtime_code, at)?;

		let at_hash = self.backend.blockchain().block_hash_from_id(at)?.ok_or_else(|| {
			sp_blockchain::Error::UnknownBlock(format!("Could not find block hash for {:?}", at))
		})?;

		let return_data = StateMachine::new(
			&state,
			&mut changes,
			&self.executor,
			method,
			call_data,
			extensions.unwrap_or_default(),
			&runtime_code,
			self.spawn_handle.clone(),
		)
		.set_parent_hash(at_hash)
		.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			strategy.get_manager(),
			None,
		)?;

		Ok(return_data.into_encoded())
	}

	fn contextual_call<
		EM: Fn(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>,
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, sp_api::ApiError> + UnwindSafe,
	>(
		&self,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		storage_transaction_cache: Option<&RefCell<StorageTransactionCache<Block, B::State>>>,
		execution_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		recorder: &Option<ProofRecorder<Block>>,
		extensions: Option<Extensions>,
	) -> Result<NativeOrEncoded<R>, sp_blockchain::Error>
	where
		ExecutionManager<EM>: Clone,
	{
		let mut storage_transaction_cache = storage_transaction_cache.map(|c| c.borrow_mut());

		let state = self.backend.state_at(*at)?;

		let changes = &mut *changes.borrow_mut();

		let at_hash = self.backend.blockchain().block_hash_from_id(at)?.ok_or_else(|| {
			sp_blockchain::Error::UnknownBlock(format!("Could not find block hash for {:?}", at))
		})?;

		// It is important to extract the runtime code here before we create the proof
		// recorder to not record it. We also need to fetch the runtime code from `state` to
		// make sure we use the caching layers.
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);

		let runtime_code =
			state_runtime_code.runtime_code().map_err(sp_blockchain::Error::RuntimeCode)?;
		let runtime_code = self.check_override(runtime_code, at)?;

		match recorder {
			Some(recorder) => {
				let trie_state = state.as_trie_backend();

				let backend = sp_state_machine::TrieBackendBuilder::wrap(&trie_state)
					.with_recorder(recorder.clone())
					.build();

				let mut state_machine = StateMachine::new(
					&backend,
					changes,
					&self.executor,
					method,
					call_data,
					extensions.unwrap_or_default(),
					&runtime_code,
					self.spawn_handle.clone(),
				)
				.with_storage_transaction_cache(storage_transaction_cache.as_deref_mut())
				.set_parent_hash(at_hash);
				state_machine.execute_using_consensus_failure_handler(
					execution_manager,
					native_call.map(|n| || (n)().map_err(|e| Box::new(e) as Box<_>)),
				)
			},
			None => {
				let mut state_machine = StateMachine::new(
					&state,
					changes,
					&self.executor,
					method,
					call_data,
					extensions.unwrap_or_default(),
					&runtime_code,
					self.spawn_handle.clone(),
				)
				.with_storage_transaction_cache(storage_transaction_cache.as_deref_mut())
				.set_parent_hash(at_hash);
				state_machine.execute_using_consensus_failure_handler(
					execution_manager,
					native_call.map(|n| || (n)().map_err(|e| Box::new(e) as Box<_>)),
				)
			},
		}
		.map_err(Into::into)
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> sp_blockchain::Result<RuntimeVersion> {
		let mut overlay = OverlayedChanges::default();
		let state = self.backend.state_at(*id)?;
		let mut cache = StorageTransactionCache::<Block, B::State>::default();
		let mut ext = Ext::new(&mut overlay, &mut cache, &state, None);
		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(&state);
		let runtime_code =
			state_runtime_code.runtime_code().map_err(sp_blockchain::Error::RuntimeCode)?;
		self.executor
			.runtime_version(&mut ext, &runtime_code)
			.map_err(|e| sp_blockchain::Error::VersionInvalid(e.to_string()))
	}

	fn prove_execution(
		&self,
		at: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
	) -> sp_blockchain::Result<(Vec<u8>, StorageProof)> {
		let state = self.backend.state_at(*at)?;

		let trie_backend = state.as_trie_backend();

		let state_runtime_code = sp_state_machine::backend::BackendRuntimeCode::new(trie_backend);
		let runtime_code =
			state_runtime_code.runtime_code().map_err(sp_blockchain::Error::RuntimeCode)?;
		let runtime_code = self.check_override(runtime_code, at)?;

		sp_state_machine::prove_execution_on_trie_backend(
			trie_backend,
			&mut Default::default(),
			&self.executor,
			self.spawn_handle.clone(),
			method,
			call_data,
			&runtime_code,
		)
		.map_err(Into::into)
	}
}

impl<B, E, Block> RuntimeVersionOf for LocalCallExecutor<Block, B, E>
where
	E: RuntimeVersionOf,
	Block: BlockT,
{
	fn runtime_version(
		&self,
		ext: &mut dyn sp_externalities::Externalities,
		runtime_code: &sp_core::traits::RuntimeCode,
	) -> Result<sp_version::RuntimeVersion, sc_executor::error::Error> {
		RuntimeVersionOf::runtime_version(&self.executor, ext, runtime_code)
	}
}

impl<Block, B, E> sp_version::GetRuntimeVersionAt<Block> for LocalCallExecutor<Block, B, E>
where
	B: backend::Backend<Block>,
	E: CodeExecutor + RuntimeVersionOf + Clone + 'static,
	Block: BlockT,
{
	fn runtime_version(&self, at: &BlockId<Block>) -> Result<sp_version::RuntimeVersion, String> {
		CallExecutor::runtime_version(self, at).map_err(|e| e.to_string())
	}
}

impl<Block, B, E> sp_version::GetNativeVersion for LocalCallExecutor<Block, B, E>
where
	B: backend::Backend<Block>,
	E: CodeExecutor + sp_version::GetNativeVersion + Clone + 'static,
	Block: BlockT,
{
	fn native_version(&self) -> &sp_version::NativeVersion {
		self.executor.native_version()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_client_api::in_mem;
	use sc_executor::{NativeElseWasmExecutor, WasmExecutionMethod};
	use sp_core::{
		testing::TaskExecutor,
		traits::{FetchRuntimeCode, WrappedRuntimeCode},
	};
	use substrate_test_runtime_client::{runtime, GenesisInit, LocalExecutorDispatch};

	#[test]
	fn should_get_override_if_exists() {
		let executor = NativeElseWasmExecutor::<LocalExecutorDispatch>::new(
			WasmExecutionMethod::Interpreted,
			Some(128),
			1,
			2,
		);

		let overrides = crate::client::wasm_override::dummy_overrides();
		let onchain_code = WrappedRuntimeCode(substrate_test_runtime::wasm_binary_unwrap().into());
		let onchain_code = RuntimeCode {
			code_fetcher: &onchain_code,
			heap_pages: Some(128),
			hash: vec![0, 0, 0, 0],
		};

		let backend = Arc::new(in_mem::Backend::<runtime::Block>::new());

		// wasm_runtime_overrides is `None` here because we construct the
		// LocalCallExecutor directly later on
		let client_config = ClientConfig::default();

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
			None,
			Default::default(),
		)
		.expect("Creates a client");

		let call_executor = LocalCallExecutor {
			backend: backend.clone(),
			executor: executor.clone(),
			wasm_override: Arc::new(Some(overrides)),
			spawn_handle: Box::new(TaskExecutor::new()),
			client_config,
			wasm_substitutes: WasmSubstitutes::new(
				Default::default(),
				executor.clone(),
				backend.clone(),
			)
			.unwrap(),
		};

		let check = call_executor
			.check_override(onchain_code, &BlockId::Number(Default::default()))
			.expect("RuntimeCode override");

		assert_eq!(Some(vec![2, 2, 2, 2, 2, 2, 2, 2]), check.fetch_runtime_code().map(Into::into));
	}
}
