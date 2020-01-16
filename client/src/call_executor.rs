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

use std::{sync::Arc, panic::UnwindSafe, result, cell::RefCell};
use codec::{Encode, Decode};
use sp_runtime::{
	generic::BlockId, traits::{Block as BlockT, HasherFor, NumberFor},
};
use sp_state_machine::{
	self, OverlayedChanges, Ext, ExecutionManager, StateMachine, ExecutionStrategy,
	backend::Backend as _, StorageProof,
};
use sc_executor::{RuntimeVersion, RuntimeInfo, NativeVersion};
use sp_externalities::Extensions;
use sp_core::{NativeOrEncoded, NeverNativeValue, traits::CodeExecutor};
use sp_api::{ProofRecorder, InitializeBlock, StorageTransactionCache};
use sc_client_api::{backend, call_executor::CallExecutor};

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
}

impl<B, E> LocalCallExecutor<B, E> {
	/// Creates new instance of local call executor.
	pub fn new(
		backend: Arc<B>,
		executor: E,
	) -> Self {
		LocalCallExecutor {
			backend,
			executor,
		}
	}
}

impl<B, E> Clone for LocalCallExecutor<B, E> where E: Clone {
	fn clone(&self) -> Self {
		LocalCallExecutor {
			backend: self.backend.clone(),
			executor: self.executor.clone(),
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
		let state = self.backend.state_at(*id)?;
		let return_data = StateMachine::new(
			&state,
			backend::changes_tries_state_at_block(id, self.backend.changes_trie_storage())?,
			&mut changes,
			&self.executor,
			method,
			call_data,
			extensions.unwrap_or_default(),
		).execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			strategy.get_manager(),
			None,
		)?;
		{
			let _lock = self.backend.get_import_lock().read();
			self.backend.destroy_state(state)?;
		}
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

		let mut state = self.backend.state_at(*at)?;
		let changes_trie_state = backend::changes_tries_state_at_block(at, self.backend.changes_trie_storage())?;

		let mut storage_transaction_cache = storage_transaction_cache.map(|c| c.borrow_mut());

		let result = match recorder {
			Some(recorder) => {
				let trie_state = state.as_trie_backend()
					.ok_or_else(||
						Box::new(sp_state_machine::ExecutionError::UnableToGenerateProof)
							as Box<dyn sp_state_machine::Error>
					)?;

				let backend = sp_state_machine::ProvingBackend::new_with_recorder(
					trie_state,
					recorder.clone(),
				);

				StateMachine::new(
					&backend,
					changes_trie_state,
					&mut *changes.borrow_mut(),
					&self.executor,
					method,
					call_data,
					extensions.unwrap_or_default(),
				)
				// TODO: https://github.com/paritytech/substrate/issues/4455
				// .with_storage_transaction_cache(storage_transaction_cache.as_mut().map(|c| &mut **c))
				.execute_using_consensus_failure_handler(execution_manager, native_call)
			}
			None => StateMachine::new(
				&state,
				changes_trie_state,
				&mut *changes.borrow_mut(),
				&self.executor,
				method,
				call_data,
				extensions.unwrap_or_default(),
			)
			.with_storage_transaction_cache(storage_transaction_cache.as_mut().map(|c| &mut **c))
			.execute_using_consensus_failure_handler(execution_manager, native_call)
		}?;
		{
			let _lock = self.backend.get_import_lock().read();
			self.backend.destroy_state(state)?;
		}
		Ok(result)
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> sp_blockchain::Result<RuntimeVersion> {
		let mut overlay = OverlayedChanges::default();
		let state = self.backend.state_at(*id)?;
		let changes_trie_state = backend::changes_tries_state_at_block(id, self.backend.changes_trie_storage())?;
		let mut cache = StorageTransactionCache::<Block, B::State>::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut cache,
			&state,
			changes_trie_state,
			None,
		);
		let version = self.executor.runtime_version(&mut ext);
		{
			let _lock = self.backend.get_import_lock().read();
			self.backend.destroy_state(state)?;
		}
		version.map_err(|e| sp_blockchain::Error::VersionInvalid(format!("{:?}", e)).into())
	}

	fn prove_at_trie_state<S: sp_state_machine::TrieBackendStorage<HasherFor<Block>>>(
		&self,
		trie_state: &sp_state_machine::TrieBackend<S, HasherFor<Block>>,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, StorageProof), sp_blockchain::Error> {
		sp_state_machine::prove_execution_on_trie_backend::<_, _, NumberFor<Block>, _>(
			trie_state,
			overlay,
			&self.executor,
			method,
			call_data,
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
