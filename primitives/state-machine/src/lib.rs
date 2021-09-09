// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate state machine implementation.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod backend;
#[cfg(feature = "std")]
mod basic;
#[cfg(feature = "std")]
mod changes_trie;
mod error;
mod ext;
#[cfg(feature = "std")]
mod in_memory_backend;
pub(crate) mod overlayed_changes;
#[cfg(feature = "std")]
mod proving_backend;
#[cfg(feature = "std")]
mod read_only;
mod stats;
#[cfg(feature = "std")]
mod testing;
mod trie_backend;
mod trie_backend_essence;

#[cfg(feature = "std")]
pub use std_reexport::*;

#[cfg(feature = "std")]
pub use execution::*;
#[cfg(feature = "std")]
pub use log::{debug, error as log_error, warn};
#[cfg(feature = "std")]
pub use tracing::trace;

/// In no_std we skip logs for state_machine, this macro
/// is a noops.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! warn {
	(target: $target:expr, $($arg:tt)+) => {
		()
	};
	($($arg:tt)+) => {
		()
	};
}

/// In no_std we skip logs for state_machine, this macro
/// is a noops.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! debug {
	(target: $target:expr, $($arg:tt)+) => {
		()
	};
	($($arg:tt)+) => {
		()
	};
}

/// In no_std we skip logs for state_machine, this macro
/// is a noops.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! trace {
	(target: $target:expr, $($arg:tt)+) => {
		()
	};
	($($arg:tt)+) => {
		()
	};
}

/// In no_std we skip logs for state_machine, this macro
/// is a noops.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! log_error {
	(target: $target:expr, $($arg:tt)+) => {
		()
	};
	($($arg:tt)+) => {
		()
	};
}

/// Default error type to use with state machine trie backend.
#[cfg(feature = "std")]
pub type DefaultError = String;
/// Error type to use with state machine trie backend.
#[cfg(not(feature = "std"))]
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct DefaultError;

#[cfg(not(feature = "std"))]
impl sp_std::fmt::Display for DefaultError {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "DefaultError")
	}
}

pub use crate::{
	backend::Backend,
	ext::Ext,
	overlayed_changes::{
		ChildStorageCollection, IndexOperation, OffchainChangesCollection,
		OffchainOverlayedChanges, OverlayedChanges, StorageChanges, StorageCollection, StorageKey,
		StorageTransactionCache, StorageValue,
	},
	stats::{StateMachineStats, UsageInfo, UsageUnit},
	trie_backend::TrieBackend,
	trie_backend_essence::{Storage, TrieBackendStorage},
};
pub use error::{Error, ExecutionError};

#[cfg(not(feature = "std"))]
mod changes_trie {
	/// Stub for change trie block number until
	/// change trie move to no_std.
	pub trait BlockNumber {}

	impl<N> BlockNumber for N {}
}

#[cfg(feature = "std")]
mod std_reexport {
	pub use crate::{
		basic::BasicExternalities,
		changes_trie::{
			disabled_state as disabled_changes_trie_state, key_changes, key_changes_proof,
			key_changes_proof_check, key_changes_proof_check_with_db, prune as prune_changes_tries,
			AnchorBlockId as ChangesTrieAnchorBlockId, BlockNumber as ChangesTrieBlockNumber,
			BuildCache as ChangesTrieBuildCache, CacheAction as ChangesTrieCacheAction,
			ConfigurationRange as ChangesTrieConfigurationRange,
			InMemoryStorage as InMemoryChangesTrieStorage, RootsStorage as ChangesTrieRootsStorage,
			State as ChangesTrieState, Storage as ChangesTrieStorage,
		},
		error::{Error, ExecutionError},
		in_memory_backend::new_in_mem,
		proving_backend::{
			create_proof_check_backend, ProofRecorder, ProvingBackend, ProvingBackendRecorder,
		},
		read_only::{InspectState, ReadOnlyExternalities},
		testing::TestExternalities,
	};
	pub use sp_trie::{
		trie_types::{Layout, TrieDBMut},
		DBValue, MemoryDB, StorageProof, TrieMut,
	};
}

#[cfg(feature = "std")]
mod execution {
	use super::*;
	use codec::{Codec, Decode, Encode};
	use hash_db::Hasher;
	use sp_core::{
		hexdisplay::HexDisplay,
		storage::ChildInfo,
		traits::{CodeExecutor, ReadRuntimeVersionExt, RuntimeCode, SpawnNamed},
		NativeOrEncoded, NeverNativeValue,
	};
	use sp_externalities::Extensions;
	use std::{collections::HashMap, fmt, panic::UnwindSafe, result};
	use tracing::{trace, warn};

	const PROOF_CLOSE_TRANSACTION: &str = "\
		Closing a transaction that was started in this function. Client initiated transactions
		are protected from being closed by the runtime. qed";

	pub(crate) type CallResult<R, E> = Result<NativeOrEncoded<R>, E>;

	/// Default handler of the execution manager.
	pub type DefaultHandler<R, E> = fn(CallResult<R, E>, CallResult<R, E>) -> CallResult<R, E>;

	/// Type of changes trie transaction.
	pub type ChangesTrieTransaction<H, N> =
		(MemoryDB<H>, ChangesTrieCacheAction<<H as Hasher>::Out, N>);

	/// Trie backend with in-memory storage.
	pub type InMemoryBackend<H> = TrieBackend<MemoryDB<H>, H>;

	/// Strategy for executing a call into the runtime.
	#[derive(Copy, Clone, Eq, PartialEq, Debug)]
	pub enum ExecutionStrategy {
		/// Execute with the native equivalent if it is compatible with the given wasm module;
		/// otherwise fall back to the wasm.
		NativeWhenPossible,
		/// Use the given wasm module.
		AlwaysWasm,
		/// Run with both the wasm and the native variant (if compatible). Report any discrepancy
		/// as an error.
		Both,
		/// First native, then if that fails or is not possible, wasm.
		NativeElseWasm,
	}

	/// Storage backend trust level.
	#[derive(Debug, Clone)]
	pub enum BackendTrustLevel {
		/// Panics from trusted backends are considered justified, and never caught.
		Trusted,
		/// Panics from untrusted backend are caught and interpreted as runtime error.
		/// Untrusted backend may be missing some parts of the trie, so panics are not considered
		/// fatal.
		Untrusted,
	}

	/// Like `ExecutionStrategy` only it also stores a handler in case of consensus failure.
	#[derive(Clone)]
	pub enum ExecutionManager<F> {
		/// Execute with the native equivalent if it is compatible with the given wasm module;
		/// otherwise fall back to the wasm.
		NativeWhenPossible,
		/// Use the given wasm module. The backend on which code is executed code could be
		/// trusted to provide all storage or not (i.e. the light client cannot be trusted to
		/// provide for all storage queries since the storage entries it has come from an external
		/// node).
		AlwaysWasm(BackendTrustLevel),
		/// Run with both the wasm and the native variant (if compatible). Call `F` in the case of
		/// any discrepancy.
		Both(F),
		/// First native, then if that fails or is not possible, wasm.
		NativeElseWasm,
	}

	impl<'a, F> From<&'a ExecutionManager<F>> for ExecutionStrategy {
		fn from(s: &'a ExecutionManager<F>) -> Self {
			match *s {
				ExecutionManager::NativeWhenPossible => ExecutionStrategy::NativeWhenPossible,
				ExecutionManager::AlwaysWasm(_) => ExecutionStrategy::AlwaysWasm,
				ExecutionManager::NativeElseWasm => ExecutionStrategy::NativeElseWasm,
				ExecutionManager::Both(_) => ExecutionStrategy::Both,
			}
		}
	}

	impl ExecutionStrategy {
		/// Gets the corresponding manager for the execution strategy.
		pub fn get_manager<E: fmt::Debug, R: Decode + Encode>(
			self,
		) -> ExecutionManager<DefaultHandler<R, E>> {
			match self {
				ExecutionStrategy::AlwaysWasm =>
					ExecutionManager::AlwaysWasm(BackendTrustLevel::Trusted),
				ExecutionStrategy::NativeWhenPossible => ExecutionManager::NativeWhenPossible,
				ExecutionStrategy::NativeElseWasm => ExecutionManager::NativeElseWasm,
				ExecutionStrategy::Both => ExecutionManager::Both(|wasm_result, native_result| {
					warn!(
						"Consensus error between wasm {:?} and native {:?}. Using wasm.",
						wasm_result, native_result,
					);
					warn!("   Native result {:?}", native_result);
					warn!("   Wasm result {:?}", wasm_result);
					wasm_result
				}),
			}
		}
	}

	/// Evaluate to ExecutionManager::NativeElseWasm, without having to figure out the type.
	pub fn native_else_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
		ExecutionManager::NativeElseWasm
	}

	/// Evaluate to ExecutionManager::AlwaysWasm with trusted backend, without having to figure out
	/// the type.
	fn always_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
		ExecutionManager::AlwaysWasm(BackendTrustLevel::Trusted)
	}

	/// Evaluate ExecutionManager::AlwaysWasm with untrusted backend, without having to figure out
	/// the type.
	fn always_untrusted_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
		ExecutionManager::AlwaysWasm(BackendTrustLevel::Untrusted)
	}

	/// The substrate state machine.
	pub struct StateMachine<'a, B, H, N, Exec>
	where
		H: Hasher,
		B: Backend<H>,
		N: ChangesTrieBlockNumber,
	{
		backend: &'a B,
		exec: &'a Exec,
		method: &'a str,
		call_data: &'a [u8],
		overlay: &'a mut OverlayedChanges,
		extensions: Extensions,
		changes_trie_state: Option<ChangesTrieState<'a, H, N>>,
		storage_transaction_cache: Option<&'a mut StorageTransactionCache<B::Transaction, H, N>>,
		runtime_code: &'a RuntimeCode<'a>,
		stats: StateMachineStats,
		/// The hash of the block the state machine will be executed on.
		///
		/// Used for logging.
		parent_hash: Option<H::Out>,
	}

	impl<'a, B, H, N, Exec> Drop for StateMachine<'a, B, H, N, Exec>
	where
		H: Hasher,
		B: Backend<H>,
		N: ChangesTrieBlockNumber,
	{
		fn drop(&mut self) {
			self.backend.register_overlay_stats(&self.stats);
		}
	}

	impl<'a, B, H, N, Exec> StateMachine<'a, B, H, N, Exec>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
		Exec: CodeExecutor + Clone + 'static,
		B: Backend<H>,
		N: crate::changes_trie::BlockNumber,
	{
		/// Creates new substrate state machine.
		pub fn new(
			backend: &'a B,
			changes_trie_state: Option<ChangesTrieState<'a, H, N>>,
			overlay: &'a mut OverlayedChanges,
			exec: &'a Exec,
			method: &'a str,
			call_data: &'a [u8],
			mut extensions: Extensions,
			runtime_code: &'a RuntimeCode,
			spawn_handle: impl SpawnNamed + Send + 'static,
		) -> Self {
			extensions.register(ReadRuntimeVersionExt::new(exec.clone()));
			extensions.register(sp_core::traits::TaskExecutorExt::new(spawn_handle));

			Self {
				backend,
				exec,
				method,
				call_data,
				extensions,
				overlay,
				changes_trie_state,
				storage_transaction_cache: None,
				runtime_code,
				stats: StateMachineStats::default(),
				parent_hash: None,
			}
		}

		/// Use given `cache` as storage transaction cache.
		///
		/// The cache will be used to cache storage transactions that can be build while executing a
		/// function in the runtime. For example, when calculating the storage root a transaction is
		/// build that will be cached.
		pub fn with_storage_transaction_cache(
			mut self,
			cache: Option<&'a mut StorageTransactionCache<B::Transaction, H, N>>,
		) -> Self {
			self.storage_transaction_cache = cache;
			self
		}

		/// Set the given `parent_hash` as the hash of the parent block.
		///
		/// This will be used for improved logging.
		pub fn set_parent_hash(mut self, parent_hash: H::Out) -> Self {
			self.parent_hash = Some(parent_hash);
			self
		}

		/// Execute a call using the given state backend, overlayed changes, and call executor.
		///
		/// On an error, no prospective changes are written to the overlay.
		///
		/// Note: changes to code will be in place if this call is made again. For running partial
		/// blocks (e.g. a transaction at a time), ensure a different method is used.
		///
		/// Returns the SCALE encoded result of the executed function.
		pub fn execute(&mut self, strategy: ExecutionStrategy) -> Result<Vec<u8>, Box<dyn Error>> {
			// We are not giving a native call and thus we are sure that the result can never be a
			// native value.
			self.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
				strategy.get_manager(),
				None,
			)
			.map(NativeOrEncoded::into_encoded)
		}

		fn execute_aux<R, NC>(
			&mut self,
			use_native: bool,
			native_call: Option<NC>,
		) -> (CallResult<R, Exec::Error>, bool)
		where
			R: Decode + Encode + PartialEq,
			NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>>
				+ UnwindSafe,
		{
			let mut cache = StorageTransactionCache::default();

			let cache = match self.storage_transaction_cache.as_mut() {
				Some(cache) => cache,
				None => &mut cache,
			};

			self.overlay
				.enter_runtime()
				.expect("StateMachine is never called from the runtime; qed");

			let mut ext = Ext::new(
				self.overlay,
				cache,
				self.backend,
				self.changes_trie_state.clone(),
				Some(&mut self.extensions),
			);

			let ext_id = ext.id;

			trace!(
				target: "state",
				ext_id = %HexDisplay::from(&ext_id.to_le_bytes()),
				method = %self.method,
				parent_hash = %self.parent_hash.map(|h| format!("{:?}", h)).unwrap_or_else(|| String::from("None")),
				input = ?HexDisplay::from(&self.call_data),
				"Call",
			);

			let (result, was_native) = self.exec.call(
				&mut ext,
				self.runtime_code,
				self.method,
				self.call_data,
				use_native,
				native_call,
			);

			self.overlay
				.exit_runtime()
				.expect("Runtime is not able to call this function in the overlay; qed");

			trace!(
				target: "state",
				ext_id = %HexDisplay::from(&ext_id.to_le_bytes()),
				?was_native,
				?result,
				"Return",
			);

			(result, was_native)
		}

		fn execute_call_with_both_strategy<Handler, R, NC>(
			&mut self,
			mut native_call: Option<NC>,
			on_consensus_failure: Handler,
		) -> CallResult<R, Exec::Error>
		where
			R: Decode + Encode + PartialEq,
			NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>>
				+ UnwindSafe,
			Handler: FnOnce(
				CallResult<R, Exec::Error>,
				CallResult<R, Exec::Error>,
			) -> CallResult<R, Exec::Error>,
		{
			self.overlay.start_transaction();
			let (result, was_native) = self.execute_aux(true, native_call.take());

			if was_native {
				self.overlay.rollback_transaction().expect(PROOF_CLOSE_TRANSACTION);
				let (wasm_result, _) = self.execute_aux(false, native_call);

				if (result.is_ok() &&
					wasm_result.is_ok() && result.as_ref().ok() == wasm_result.as_ref().ok()) ||
					result.is_err() && wasm_result.is_err()
				{
					result
				} else {
					on_consensus_failure(wasm_result, result)
				}
			} else {
				self.overlay.commit_transaction().expect(PROOF_CLOSE_TRANSACTION);
				result
			}
		}

		fn execute_call_with_native_else_wasm_strategy<R, NC>(
			&mut self,
			mut native_call: Option<NC>,
		) -> CallResult<R, Exec::Error>
		where
			R: Decode + Encode + PartialEq,
			NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>>
				+ UnwindSafe,
		{
			self.overlay.start_transaction();
			let (result, was_native) = self.execute_aux(true, native_call.take());

			if !was_native || result.is_ok() {
				self.overlay.commit_transaction().expect(PROOF_CLOSE_TRANSACTION);
				result
			} else {
				self.overlay.rollback_transaction().expect(PROOF_CLOSE_TRANSACTION);
				let (wasm_result, _) = self.execute_aux(false, native_call);
				wasm_result
			}
		}

		/// Execute a call using the given state backend, overlayed changes, and call executor.
		///
		/// On an error, no prospective changes are written to the overlay.
		///
		/// Note: changes to code will be in place if this call is made again. For running partial
		/// blocks (e.g. a transaction at a time), ensure a different method is used.
		///
		/// Returns the result of the executed function either in native representation `R` or
		/// in SCALE encoded representation.
		pub fn execute_using_consensus_failure_handler<Handler, R, NC>(
			&mut self,
			manager: ExecutionManager<Handler>,
			mut native_call: Option<NC>,
		) -> Result<NativeOrEncoded<R>, Box<dyn Error>>
		where
			R: Decode + Encode + PartialEq,
			NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>>
				+ UnwindSafe,
			Handler: FnOnce(
				CallResult<R, Exec::Error>,
				CallResult<R, Exec::Error>,
			) -> CallResult<R, Exec::Error>,
		{
			let changes_tries_enabled = self.changes_trie_state.is_some();
			self.overlay.set_collect_extrinsics(changes_tries_enabled);

			let result = {
				match manager {
					ExecutionManager::Both(on_consensus_failure) => self
						.execute_call_with_both_strategy(native_call.take(), on_consensus_failure),
					ExecutionManager::NativeElseWasm =>
						self.execute_call_with_native_else_wasm_strategy(native_call.take()),
					ExecutionManager::AlwaysWasm(trust_level) => {
						let _abort_guard = match trust_level {
							BackendTrustLevel::Trusted => None,
							BackendTrustLevel::Untrusted =>
								Some(sp_panic_handler::AbortGuard::never_abort()),
						};
						self.execute_aux(false, native_call).0
					},
					ExecutionManager::NativeWhenPossible => self.execute_aux(true, native_call).0,
				}
			};

			result.map_err(|e| Box::new(e) as _)
		}
	}

	/// Prove execution using the given state backend, overlayed changes, and call executor.
	pub fn prove_execution<B, H, N, Exec, Spawn>(
		backend: &mut B,
		overlay: &mut OverlayedChanges,
		exec: &Exec,
		spawn_handle: Spawn,
		method: &str,
		call_data: &[u8],
		runtime_code: &RuntimeCode,
	) -> Result<(Vec<u8>, StorageProof), Box<dyn Error>>
	where
		B: Backend<H>,
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
		Exec: CodeExecutor + Clone + 'static,
		N: crate::changes_trie::BlockNumber,
		Spawn: SpawnNamed + Send + 'static,
	{
		let trie_backend = backend
			.as_trie_backend()
			.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
		prove_execution_on_trie_backend::<_, _, N, _, _>(
			trie_backend,
			overlay,
			exec,
			spawn_handle,
			method,
			call_data,
			runtime_code,
		)
	}

	/// Prove execution using the given trie backend, overlayed changes, and call executor.
	/// Produces a state-backend-specific "transaction" which can be used to apply the changes
	/// to the backing store, such as the disk.
	/// Execution proof is the set of all 'touched' storage DBValues from the backend.
	///
	/// On an error, no prospective changes are written to the overlay.
	///
	/// Note: changes to code will be in place if this call is made again. For running partial
	/// blocks (e.g. a transaction at a time), ensure a different method is used.
	pub fn prove_execution_on_trie_backend<S, H, N, Exec, Spawn>(
		trie_backend: &TrieBackend<S, H>,
		overlay: &mut OverlayedChanges,
		exec: &Exec,
		spawn_handle: Spawn,
		method: &str,
		call_data: &[u8],
		runtime_code: &RuntimeCode,
	) -> Result<(Vec<u8>, StorageProof), Box<dyn Error>>
	where
		S: trie_backend_essence::TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
		Exec: CodeExecutor + 'static + Clone,
		N: crate::changes_trie::BlockNumber,
		Spawn: SpawnNamed + Send + 'static,
	{
		let proving_backend = proving_backend::ProvingBackend::new(trie_backend);
		let mut sm = StateMachine::<_, H, N, Exec>::new(
			&proving_backend,
			None,
			overlay,
			exec,
			method,
			call_data,
			Extensions::default(),
			runtime_code,
			spawn_handle,
		);

		let result = sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			always_wasm(),
			None,
		)?;
		let proof = sm.backend.extract_proof();
		Ok((result.into_encoded(), proof))
	}

	/// Check execution proof, generated by `prove_execution` call.
	pub fn execution_proof_check<H, N, Exec, Spawn>(
		root: H::Out,
		proof: StorageProof,
		overlay: &mut OverlayedChanges,
		exec: &Exec,
		spawn_handle: Spawn,
		method: &str,
		call_data: &[u8],
		runtime_code: &RuntimeCode,
	) -> Result<Vec<u8>, Box<dyn Error>>
	where
		H: Hasher,
		Exec: CodeExecutor + Clone + 'static,
		H::Out: Ord + 'static + codec::Codec,
		N: crate::changes_trie::BlockNumber,
		Spawn: SpawnNamed + Send + 'static,
	{
		let trie_backend = create_proof_check_backend::<H>(root.into(), proof)?;
		execution_proof_check_on_trie_backend::<_, N, _, _>(
			&trie_backend,
			overlay,
			exec,
			spawn_handle,
			method,
			call_data,
			runtime_code,
		)
	}

	/// Check execution proof on proving backend, generated by `prove_execution` call.
	pub fn execution_proof_check_on_trie_backend<H, N, Exec, Spawn>(
		trie_backend: &TrieBackend<MemoryDB<H>, H>,
		overlay: &mut OverlayedChanges,
		exec: &Exec,
		spawn_handle: Spawn,
		method: &str,
		call_data: &[u8],
		runtime_code: &RuntimeCode,
	) -> Result<Vec<u8>, Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
		Exec: CodeExecutor + Clone + 'static,
		N: crate::changes_trie::BlockNumber,
		Spawn: SpawnNamed + Send + 'static,
	{
		let mut sm = StateMachine::<_, H, N, Exec>::new(
			trie_backend,
			None,
			overlay,
			exec,
			method,
			call_data,
			Extensions::default(),
			runtime_code,
			spawn_handle,
		);

		sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			always_untrusted_wasm(),
			None,
		)
		.map(NativeOrEncoded::into_encoded)
	}

	/// Generate storage read proof.
	pub fn prove_read<B, H, I>(backend: B, keys: I) -> Result<StorageProof, Box<dyn Error>>
	where
		B: Backend<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let trie_backend = backend
			.as_trie_backend()
			.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
		prove_read_on_trie_backend(trie_backend, keys)
	}

	/// Generate range storage read proof.
	pub fn prove_range_read_with_size<B, H>(
		backend: B,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		size_limit: usize,
		start_at: Option<&[u8]>,
	) -> Result<(StorageProof, u32), Box<dyn Error>>
	where
		B: Backend<H>,
		H: Hasher,
		H::Out: Ord + Codec,
	{
		let trie_backend = backend
			.as_trie_backend()
			.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
		prove_range_read_with_size_on_trie_backend(
			trie_backend,
			child_info,
			prefix,
			size_limit,
			start_at,
		)
	}

	/// Generate range storage read proof on an existing trie backend.
	pub fn prove_range_read_with_size_on_trie_backend<S, H>(
		trie_backend: &TrieBackend<S, H>,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		size_limit: usize,
		start_at: Option<&[u8]>,
	) -> Result<(StorageProof, u32), Box<dyn Error>>
	where
		S: trie_backend_essence::TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + Codec,
	{
		let proving_backend = proving_backend::ProvingBackend::<S, H>::new(trie_backend);
		let mut count = 0;
		proving_backend
			.apply_to_key_values_while(
				child_info,
				prefix,
				start_at,
				|_key, _value| {
					if count == 0 || proving_backend.estimate_encoded_size() <= size_limit {
						count += 1;
						true
					} else {
						false
					}
				},
				false,
			)
			.map_err(|e| Box::new(e) as Box<dyn Error>)?;
		Ok((proving_backend.extract_proof(), count))
	}

	/// Generate child storage read proof.
	pub fn prove_child_read<B, H, I>(
		backend: B,
		child_info: &ChildInfo,
		keys: I,
	) -> Result<StorageProof, Box<dyn Error>>
	where
		B: Backend<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let trie_backend = backend
			.as_trie_backend()
			.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
		prove_child_read_on_trie_backend(trie_backend, child_info, keys)
	}

	/// Generate storage read proof on pre-created trie backend.
	pub fn prove_read_on_trie_backend<S, H, I>(
		trie_backend: &TrieBackend<S, H>,
		keys: I,
	) -> Result<StorageProof, Box<dyn Error>>
	where
		S: trie_backend_essence::TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
		for key in keys.into_iter() {
			proving_backend
				.storage(key.as_ref())
				.map_err(|e| Box::new(e) as Box<dyn Error>)?;
		}
		Ok(proving_backend.extract_proof())
	}

	/// Generate storage read proof on pre-created trie backend.
	pub fn prove_child_read_on_trie_backend<S, H, I>(
		trie_backend: &TrieBackend<S, H>,
		child_info: &ChildInfo,
		keys: I,
	) -> Result<StorageProof, Box<dyn Error>>
	where
		S: trie_backend_essence::TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
		for key in keys.into_iter() {
			proving_backend
				.child_storage(child_info, key.as_ref())
				.map_err(|e| Box::new(e) as Box<dyn Error>)?;
		}
		Ok(proving_backend.extract_proof())
	}

	/// Check storage read proof, generated by `prove_read` call.
	pub fn read_proof_check<H, I>(
		root: H::Out,
		proof: StorageProof,
		keys: I,
	) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let proving_backend = create_proof_check_backend::<H>(root, proof)?;
		let mut result = HashMap::new();
		for key in keys.into_iter() {
			let value = read_proof_check_on_proving_backend(&proving_backend, key.as_ref())?;
			result.insert(key.as_ref().to_vec(), value);
		}
		Ok(result)
	}

	/// Check child storage range proof, generated by `prove_range_read` call.
	pub fn read_range_proof_check<H>(
		root: H::Out,
		proof: StorageProof,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		count: Option<u32>,
		start_at: Option<&[u8]>,
	) -> Result<(Vec<(Vec<u8>, Vec<u8>)>, bool), Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
	{
		let proving_backend = create_proof_check_backend::<H>(root, proof)?;
		read_range_proof_check_on_proving_backend(
			&proving_backend,
			child_info,
			prefix,
			count,
			start_at,
		)
	}

	/// Check child storage read proof, generated by `prove_child_read` call.
	pub fn read_child_proof_check<H, I>(
		root: H::Out,
		proof: StorageProof,
		child_info: &ChildInfo,
		keys: I,
	) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		let proving_backend = create_proof_check_backend::<H>(root, proof)?;
		let mut result = HashMap::new();
		for key in keys.into_iter() {
			let value = read_child_proof_check_on_proving_backend(
				&proving_backend,
				child_info,
				key.as_ref(),
			)?;
			result.insert(key.as_ref().to_vec(), value);
		}
		Ok(result)
	}

	/// Check storage read proof on pre-created proving backend.
	pub fn read_proof_check_on_proving_backend<H>(
		proving_backend: &TrieBackend<MemoryDB<H>, H>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
	{
		proving_backend.storage(key).map_err(|e| Box::new(e) as Box<dyn Error>)
	}

	/// Check child storage read proof on pre-created proving backend.
	pub fn read_child_proof_check_on_proving_backend<H>(
		proving_backend: &TrieBackend<MemoryDB<H>, H>,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
	{
		proving_backend
			.child_storage(child_info, key)
			.map_err(|e| Box::new(e) as Box<dyn Error>)
	}

	/// Check storage range proof on pre-created proving backend.
	///
	/// Returns a vector with the read `key => value` pairs and a `bool` that is set to `true` when
	/// all `key => value` pairs could be read and no more are left.
	pub fn read_range_proof_check_on_proving_backend<H>(
		proving_backend: &TrieBackend<MemoryDB<H>, H>,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		count: Option<u32>,
		start_at: Option<&[u8]>,
	) -> Result<(Vec<(Vec<u8>, Vec<u8>)>, bool), Box<dyn Error>>
	where
		H: Hasher,
		H::Out: Ord + Codec,
	{
		let mut values = Vec::new();
		let result = proving_backend.apply_to_key_values_while(
			child_info,
			prefix,
			start_at,
			|key, value| {
				values.push((key.to_vec(), value.to_vec()));
				count.as_ref().map_or(true, |c| (values.len() as u32) < *c)
			},
			true,
		);
		match result {
			Ok(completed) => Ok((values, completed)),
			Err(e) => Err(Box::new(e) as Box<dyn Error>),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{changes_trie::Configuration as ChangesTrieConfig, ext::Ext, *};
	use crate::execution::CallResult;
	use codec::{Decode, Encode};
	use sp_core::{
		map,
		storage::ChildInfo,
		testing::TaskExecutor,
		traits::{CodeExecutor, Externalities, RuntimeCode},
		NativeOrEncoded, NeverNativeValue,
	};
	use sp_runtime::traits::BlakeTwo256;
	use std::{
		collections::{BTreeMap, HashMap},
		panic::UnwindSafe,
		result,
	};

	#[derive(Clone)]
	struct DummyCodeExecutor {
		change_changes_trie_config: bool,
		native_available: bool,
		native_succeeds: bool,
		fallback_succeeds: bool,
	}

	impl CodeExecutor for DummyCodeExecutor {
		type Error = u8;

		fn call<
			R: Encode + Decode + PartialEq,
			NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>> + UnwindSafe,
		>(
			&self,
			ext: &mut dyn Externalities,
			_: &RuntimeCode,
			_method: &str,
			_data: &[u8],
			use_native: bool,
			native_call: Option<NC>,
		) -> (CallResult<R, Self::Error>, bool) {
			if self.change_changes_trie_config {
				ext.place_storage(
					sp_core::storage::well_known_keys::CHANGES_TRIE_CONFIG.to_vec(),
					Some(ChangesTrieConfig { digest_interval: 777, digest_levels: 333 }.encode()),
				);
			}

			let using_native = use_native && self.native_available;
			match (using_native, self.native_succeeds, self.fallback_succeeds, native_call) {
				(true, true, _, Some(call)) => {
					let res = sp_externalities::set_and_run_with_externalities(ext, || call());
					(res.map(NativeOrEncoded::Native).map_err(|_| 0), true)
				},
				(true, true, _, None) | (false, _, true, None) => (
					Ok(NativeOrEncoded::Encoded(vec![
						ext.storage(b"value1").unwrap()[0] + ext.storage(b"value2").unwrap()[0],
					])),
					using_native,
				),
				_ => (Err(0), using_native),
			}
		}
	}

	impl sp_core::traits::ReadRuntimeVersion for DummyCodeExecutor {
		fn read_runtime_version(
			&self,
			_: &[u8],
			_: &mut dyn Externalities,
		) -> std::result::Result<Vec<u8>, String> {
			unimplemented!("Not required in tests.")
		}
	}

	#[test]
	fn execute_works() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let wasm_code = RuntimeCode::empty();

		let mut state_machine = StateMachine::new(
			&backend,
			changes_trie::disabled_state::<_, u64>(),
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			Default::default(),
			&wasm_code,
			TaskExecutor::new(),
		);

		assert_eq!(state_machine.execute(ExecutionStrategy::NativeWhenPossible).unwrap(), vec![66]);
	}

	#[test]
	fn execute_works_with_native_else_wasm() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let wasm_code = RuntimeCode::empty();

		let mut state_machine = StateMachine::new(
			&backend,
			changes_trie::disabled_state::<_, u64>(),
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			Default::default(),
			&wasm_code,
			TaskExecutor::new(),
		);

		assert_eq!(state_machine.execute(ExecutionStrategy::NativeElseWasm).unwrap(), vec![66]);
	}

	#[test]
	fn dual_execution_strategy_detects_consensus_failure() {
		let mut consensus_failed = false;
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let wasm_code = RuntimeCode::empty();

		let mut state_machine = StateMachine::new(
			&backend,
			changes_trie::disabled_state::<_, u64>(),
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: false,
			},
			"test",
			&[],
			Default::default(),
			&wasm_code,
			TaskExecutor::new(),
		);

		assert!(state_machine
			.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
				ExecutionManager::Both(|we, _ne| {
					consensus_failed = true;
					we
				}),
				None,
			)
			.is_err());
		assert!(consensus_failed);
	}

	#[test]
	fn prove_execution_and_proof_check_works() {
		let executor = DummyCodeExecutor {
			change_changes_trie_config: false,
			native_available: true,
			native_succeeds: true,
			fallback_succeeds: true,
		};

		// fetch execution proof from 'remote' full node
		let mut remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(std::iter::empty()).0;
		let (remote_result, remote_proof) = prove_execution::<_, _, u64, _, _>(
			&mut remote_backend,
			&mut Default::default(),
			&executor,
			TaskExecutor::new(),
			"test",
			&[],
			&RuntimeCode::empty(),
		)
		.unwrap();

		// check proof locally
		let local_result = execution_proof_check::<BlakeTwo256, u64, _, _>(
			remote_root,
			remote_proof,
			&mut Default::default(),
			&executor,
			TaskExecutor::new(),
			"test",
			&[],
			&RuntimeCode::empty(),
		)
		.unwrap();

		// check that both results are correct
		assert_eq!(remote_result, vec![66]);
		assert_eq!(remote_result, local_result);
	}

	#[test]
	fn clear_prefix_in_ext_works() {
		let initial: BTreeMap<_, _> = map![
			b"aaa".to_vec() => b"0".to_vec(),
			b"abb".to_vec() => b"1".to_vec(),
			b"abc".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"3".to_vec()
		];
		let state = InMemoryBackend::<BlakeTwo256>::from(initial);
		let backend = state.as_trie_backend().unwrap();

		let mut overlay = OverlayedChanges::default();
		overlay.set_storage(b"aba".to_vec(), Some(b"1312".to_vec()));
		overlay.set_storage(b"bab".to_vec(), Some(b"228".to_vec()));
		overlay.start_transaction();
		overlay.set_storage(b"abd".to_vec(), Some(b"69".to_vec()));
		overlay.set_storage(b"bbd".to_vec(), Some(b"42".to_vec()));

		let overlay_limit = overlay.clone();
		{
			let mut cache = StorageTransactionCache::default();
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			ext.clear_prefix(b"ab", None);
		}
		overlay.commit_transaction().unwrap();

		assert_eq!(
			overlay
				.changes()
				.map(|(k, v)| (k.clone(), v.value().cloned()))
				.collect::<HashMap<_, _>>(),
			map![
				b"abc".to_vec() => None.into(),
				b"abb".to_vec() => None.into(),
				b"aba".to_vec() => None.into(),
				b"abd".to_vec() => None.into(),

				b"bab".to_vec() => Some(b"228".to_vec()).into(),
				b"bbd".to_vec() => Some(b"42".to_vec()).into()
			],
		);

		let mut overlay = overlay_limit;
		{
			let mut cache = StorageTransactionCache::default();
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			assert_eq!((false, 1), ext.clear_prefix(b"ab", Some(1)));
		}
		overlay.commit_transaction().unwrap();

		assert_eq!(
			overlay
				.changes()
				.map(|(k, v)| (k.clone(), v.value().cloned()))
				.collect::<HashMap<_, _>>(),
			map![
				b"abb".to_vec() => None.into(),
				b"aba".to_vec() => None.into(),
				b"abd".to_vec() => None.into(),

				b"bab".to_vec() => Some(b"228".to_vec()).into(),
				b"bbd".to_vec() => Some(b"42".to_vec()).into()
			],
		);
	}

	#[test]
	fn limited_child_kill_works() {
		let child_info = ChildInfo::new_default(b"sub1");
		let initial: HashMap<_, BTreeMap<_, _>> = map![
			Some(child_info.clone()) => map![
				b"a".to_vec() => b"0".to_vec(),
				b"b".to_vec() => b"1".to_vec(),
				b"c".to_vec() => b"2".to_vec(),
				b"d".to_vec() => b"3".to_vec()
			],
		];
		let backend = InMemoryBackend::<BlakeTwo256>::from(initial);

		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(&child_info, b"1".to_vec(), Some(b"1312".to_vec()));
		overlay.set_child_storage(&child_info, b"2".to_vec(), Some(b"1312".to_vec()));
		overlay.set_child_storage(&child_info, b"3".to_vec(), Some(b"1312".to_vec()));
		overlay.set_child_storage(&child_info, b"4".to_vec(), Some(b"1312".to_vec()));

		{
			let mut cache = StorageTransactionCache::default();
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				&backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			assert_eq!(ext.kill_child_storage(&child_info, Some(2)), (false, 2));
		}

		assert_eq!(
			overlay
				.children()
				.flat_map(|(iter, _child_info)| iter)
				.map(|(k, v)| (k.clone(), v.value().clone()))
				.collect::<BTreeMap<_, _>>(),
			map![
				b"1".to_vec() => None.into(),
				b"2".to_vec() => None.into(),
				b"3".to_vec() => None.into(),
				b"4".to_vec() => None.into(),
				b"a".to_vec() => None.into(),
				b"b".to_vec() => None.into(),
			],
		);
	}

	#[test]
	fn limited_child_kill_off_by_one_works() {
		let child_info = ChildInfo::new_default(b"sub1");
		let initial: HashMap<_, BTreeMap<_, _>> = map![
			Some(child_info.clone()) => map![
				b"a".to_vec() => b"0".to_vec(),
				b"b".to_vec() => b"1".to_vec(),
				b"c".to_vec() => b"2".to_vec(),
				b"d".to_vec() => b"3".to_vec()
			],
		];
		let backend = InMemoryBackend::<BlakeTwo256>::from(initial);
		let mut overlay = OverlayedChanges::default();
		let mut cache = StorageTransactionCache::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut cache,
			&backend,
			changes_trie::disabled_state::<_, u64>(),
			None,
		);
		assert_eq!(ext.kill_child_storage(&child_info, Some(0)), (false, 0));
		assert_eq!(ext.kill_child_storage(&child_info, Some(1)), (false, 1));
		assert_eq!(ext.kill_child_storage(&child_info, Some(2)), (false, 2));
		assert_eq!(ext.kill_child_storage(&child_info, Some(3)), (false, 3));
		assert_eq!(ext.kill_child_storage(&child_info, Some(4)), (true, 4));
		// Only 4 items to remove
		assert_eq!(ext.kill_child_storage(&child_info, Some(5)), (true, 4));
		assert_eq!(ext.kill_child_storage(&child_info, None), (true, 4));
	}

	#[test]
	fn set_child_storage_works() {
		let child_info = ChildInfo::new_default(b"sub1");
		let child_info = &child_info;
		let state = new_in_mem::<BlakeTwo256>();
		let backend = state.as_trie_backend().unwrap();
		let mut overlay = OverlayedChanges::default();
		let mut cache = StorageTransactionCache::default();
		let mut ext = Ext::new(
			&mut overlay,
			&mut cache,
			backend,
			changes_trie::disabled_state::<_, u64>(),
			None,
		);

		ext.set_child_storage(child_info, b"abc".to_vec(), b"def".to_vec());
		assert_eq!(ext.child_storage(child_info, b"abc"), Some(b"def".to_vec()));
		ext.kill_child_storage(child_info, None);
		assert_eq!(ext.child_storage(child_info, b"abc"), None);
	}

	#[test]
	fn append_storage_works() {
		let reference_data = vec![b"data1".to_vec(), b"2".to_vec(), b"D3".to_vec(), b"d4".to_vec()];
		let key = b"key".to_vec();
		let state = new_in_mem::<BlakeTwo256>();
		let backend = state.as_trie_backend().unwrap();
		let mut overlay = OverlayedChanges::default();
		let mut cache = StorageTransactionCache::default();
		{
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);

			ext.storage_append(key.clone(), reference_data[0].encode());
			assert_eq!(ext.storage(key.as_slice()), Some(vec![reference_data[0].clone()].encode()));
		}
		overlay.start_transaction();
		{
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);

			for i in reference_data.iter().skip(1) {
				ext.storage_append(key.clone(), i.encode());
			}
			assert_eq!(ext.storage(key.as_slice()), Some(reference_data.encode()));
		}
		overlay.rollback_transaction().unwrap();
		{
			let ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			assert_eq!(ext.storage(key.as_slice()), Some(vec![reference_data[0].clone()].encode()));
		}
	}

	#[test]
	fn remove_with_append_then_rollback_appended_then_append_again() {
		#[derive(codec::Encode, codec::Decode)]
		enum Item {
			InitializationItem,
			DiscardedItem,
			CommitedItem,
		}

		let key = b"events".to_vec();
		let mut cache = StorageTransactionCache::default();
		let state = new_in_mem::<BlakeTwo256>();
		let backend = state.as_trie_backend().unwrap();
		let mut overlay = OverlayedChanges::default();

		// For example, block initialization with event.
		{
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			ext.clear_storage(key.as_slice());
			ext.storage_append(key.clone(), Item::InitializationItem.encode());
		}
		overlay.start_transaction();

		// For example, first transaction resulted in panic during block building
		{
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);

			assert_eq!(ext.storage(key.as_slice()), Some(vec![Item::InitializationItem].encode()));

			ext.storage_append(key.clone(), Item::DiscardedItem.encode());

			assert_eq!(
				ext.storage(key.as_slice()),
				Some(vec![Item::InitializationItem, Item::DiscardedItem].encode()),
			);
		}
		overlay.rollback_transaction().unwrap();

		// Then we apply next transaction which is valid this time.
		{
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);

			assert_eq!(ext.storage(key.as_slice()), Some(vec![Item::InitializationItem].encode()));

			ext.storage_append(key.clone(), Item::CommitedItem.encode());

			assert_eq!(
				ext.storage(key.as_slice()),
				Some(vec![Item::InitializationItem, Item::CommitedItem].encode()),
			);
		}
		overlay.start_transaction();

		// Then only initlaization item and second (commited) item should persist.
		{
			let ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			assert_eq!(
				ext.storage(key.as_slice()),
				Some(vec![Item::InitializationItem, Item::CommitedItem].encode()),
			);
		}
	}

	fn test_compact(remote_proof: StorageProof, remote_root: &sp_core::H256) -> StorageProof {
		let compact_remote_proof =
			remote_proof.into_compact_proof::<BlakeTwo256>(remote_root.clone()).unwrap();
		compact_remote_proof
			.to_storage_proof::<BlakeTwo256>(Some(remote_root))
			.unwrap()
			.0
	}

	#[test]
	fn prove_read_and_proof_check_works() {
		let child_info = ChildInfo::new_default(b"sub1");
		let missing_child_info = ChildInfo::new_default(b"sub1sub2"); // key will include other child root to proof.
		let child_info = &child_info;
		let missing_child_info = &missing_child_info;
		// fetch read proof from 'remote' full node
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(std::iter::empty()).0;
		let remote_proof = prove_read(remote_backend, &[b"value2"]).unwrap();
		let remote_proof = test_compact(remote_proof, &remote_root);
		// check proof locally
		let local_result1 =
			read_proof_check::<BlakeTwo256, _>(remote_root, remote_proof.clone(), &[b"value2"])
				.unwrap();
		let local_result2 =
			read_proof_check::<BlakeTwo256, _>(remote_root, remote_proof.clone(), &[&[0xff]])
				.is_ok();
		// check that results are correct
		assert_eq!(
			local_result1.into_iter().collect::<Vec<_>>(),
			vec![(b"value2".to_vec(), Some(vec![24]))],
		);
		assert_eq!(local_result2, false);
		// on child trie
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(std::iter::empty()).0;
		let remote_proof = prove_child_read(remote_backend, child_info, &[b"value3"]).unwrap();
		let remote_proof = test_compact(remote_proof, &remote_root);
		let local_result1 = read_child_proof_check::<BlakeTwo256, _>(
			remote_root,
			remote_proof.clone(),
			child_info,
			&[b"value3"],
		)
		.unwrap();
		let local_result2 = read_child_proof_check::<BlakeTwo256, _>(
			remote_root,
			remote_proof.clone(),
			child_info,
			&[b"value2"],
		)
		.unwrap();
		let local_result3 = read_child_proof_check::<BlakeTwo256, _>(
			remote_root,
			remote_proof.clone(),
			missing_child_info,
			&[b"dummy"],
		)
		.unwrap();

		assert_eq!(
			local_result1.into_iter().collect::<Vec<_>>(),
			vec![(b"value3".to_vec(), Some(vec![142]))],
		);
		assert_eq!(local_result2.into_iter().collect::<Vec<_>>(), vec![(b"value2".to_vec(), None)]);
		assert_eq!(local_result3.into_iter().collect::<Vec<_>>(), vec![(b"dummy".to_vec(), None)]);
	}

	#[test]
	fn child_read_compact_stress_test() {
		use rand::{rngs::SmallRng, RngCore, SeedableRng};
		let mut storage: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>> =
			Default::default();
		let mut seed = [0; 16];
		for i in 0..50u32 {
			let mut child_infos = Vec::new();
			&seed[0..4].copy_from_slice(&i.to_be_bytes()[..]);
			let mut rand = SmallRng::from_seed(seed);

			let nb_child_trie = rand.next_u32() as usize % 25;
			for _ in 0..nb_child_trie {
				let key_len = 1 + (rand.next_u32() % 10);
				let mut key = vec![0; key_len as usize];
				rand.fill_bytes(&mut key[..]);
				let child_info = ChildInfo::new_default(key.as_slice());
				let nb_item = 1 + rand.next_u32() % 25;
				let mut items = BTreeMap::new();
				for item in 0..nb_item {
					let key_len = 1 + (rand.next_u32() % 10);
					let mut key = vec![0; key_len as usize];
					rand.fill_bytes(&mut key[..]);
					let value = vec![item as u8; item as usize + 28];
					items.insert(key, value);
				}
				child_infos.push(child_info.clone());
				storage.insert(Some(child_info), items);
			}

			let trie: InMemoryBackend<BlakeTwo256> = storage.clone().into();
			let trie_root = trie.root().clone();
			let backend = crate::ProvingBackend::new(&trie);
			let mut queries = Vec::new();
			for c in 0..(5 + nb_child_trie / 2) {
				// random existing query
				let child_info = if c < 5 {
					// 4 missing child trie
					let key_len = 1 + (rand.next_u32() % 10);
					let mut key = vec![0; key_len as usize];
					rand.fill_bytes(&mut key[..]);
					ChildInfo::new_default(key.as_slice())
				} else {
					child_infos[rand.next_u32() as usize % nb_child_trie].clone()
				};

				if let Some(values) = storage.get(&Some(child_info.clone())) {
					for _ in 0..(1 + values.len() / 2) {
						let ix = rand.next_u32() as usize % values.len();
						for (i, (key, value)) in values.iter().enumerate() {
							if i == ix {
								assert_eq!(
									&backend
										.child_storage(&child_info, key.as_slice())
										.unwrap()
										.unwrap(),
									value
								);
								queries.push((
									child_info.clone(),
									key.clone(),
									Some(value.clone()),
								));
								break
							}
						}
					}
				}
				for _ in 0..4 {
					let key_len = 1 + (rand.next_u32() % 10);
					let mut key = vec![0; key_len as usize];
					rand.fill_bytes(&mut key[..]);
					let result = backend.child_storage(&child_info, key.as_slice()).unwrap();
					queries.push((child_info.clone(), key, result));
				}
			}

			let storage_proof = backend.extract_proof();
			let remote_proof = test_compact(storage_proof, &trie_root);
			let proof_check =
				create_proof_check_backend::<BlakeTwo256>(trie_root, remote_proof).unwrap();

			for (child_info, key, expected) in queries {
				assert_eq!(
					proof_check.child_storage(&child_info, key.as_slice()).unwrap(),
					expected,
				);
			}
		}
	}

	#[test]
	fn prove_read_with_size_limit_works() {
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let (proof, count) =
			prove_range_read_with_size(remote_backend, None, None, 0, None).unwrap();
		// Alwasys contains at least some nodes.
		assert_eq!(proof.into_memory_db::<BlakeTwo256>().drain().len(), 3);
		assert_eq!(count, 1);

		let remote_backend = trie_backend::tests::test_trie();
		let (proof, count) =
			prove_range_read_with_size(remote_backend, None, None, 800, Some(&[])).unwrap();
		assert_eq!(proof.clone().into_memory_db::<BlakeTwo256>().drain().len(), 9);
		assert_eq!(count, 85);
		let (results, completed) = read_range_proof_check::<BlakeTwo256>(
			remote_root,
			proof.clone(),
			None,
			None,
			Some(count),
			None,
		)
		.unwrap();
		assert_eq!(results.len() as u32, count);
		assert_eq!(completed, false);
		// When checking without count limit, proof may actually contain extra values.
		let (results, completed) =
			read_range_proof_check::<BlakeTwo256>(remote_root, proof, None, None, None, None)
				.unwrap();
		assert_eq!(results.len() as u32, 101);
		assert_eq!(completed, false);

		let remote_backend = trie_backend::tests::test_trie();
		let (proof, count) =
			prove_range_read_with_size(remote_backend, None, None, 50000, Some(&[])).unwrap();
		assert_eq!(proof.clone().into_memory_db::<BlakeTwo256>().drain().len(), 11);
		assert_eq!(count, 132);
		let (results, completed) = read_range_proof_check::<BlakeTwo256>(
			remote_root,
			proof.clone(),
			None,
			None,
			None,
			None,
		)
		.unwrap();
		assert_eq!(results.len() as u32, count);
		assert_eq!(completed, true);
	}

	#[test]
	fn compact_multiple_child_trie() {
		// this root will be queried
		let child_info1 = ChildInfo::new_default(b"sub1");
		// this root will not be include in proof
		let child_info2 = ChildInfo::new_default(b"sub2");
		// this root will be include in proof
		let child_info3 = ChildInfo::new_default(b"sub");
		let remote_backend = trie_backend::tests::test_trie();
		let (remote_root, transaction) = remote_backend.full_storage_root(
			std::iter::empty(),
			vec![
				(
					&child_info1,
					vec![(&b"key1"[..], Some(&b"val2"[..])), (&b"key2"[..], Some(&b"val3"[..]))]
						.into_iter(),
				),
				(
					&child_info2,
					vec![(&b"key3"[..], Some(&b"val4"[..])), (&b"key4"[..], Some(&b"val5"[..]))]
						.into_iter(),
				),
				(
					&child_info3,
					vec![(&b"key5"[..], Some(&b"val6"[..])), (&b"key6"[..], Some(&b"val7"[..]))]
						.into_iter(),
				),
			]
			.into_iter(),
		);
		let mut remote_storage = remote_backend.into_storage();
		remote_storage.consolidate(transaction);
		let remote_backend = TrieBackend::new(remote_storage, remote_root);
		let remote_proof = prove_child_read(remote_backend, &child_info1, &[b"key1"]).unwrap();
		let remote_proof = test_compact(remote_proof, &remote_root);
		let local_result1 = read_child_proof_check::<BlakeTwo256, _>(
			remote_root,
			remote_proof.clone(),
			&child_info1,
			&[b"key1"],
		)
		.unwrap();
		assert_eq!(local_result1.len(), 1);
		assert_eq!(local_result1.get(&b"key1"[..]), Some(&Some(b"val2".to_vec())));
	}

	#[test]
	fn child_storage_uuid() {
		let child_info_1 = ChildInfo::new_default(b"sub_test1");
		let child_info_2 = ChildInfo::new_default(b"sub_test2");

		use crate::trie_backend::tests::test_trie;
		let mut overlay = OverlayedChanges::default();

		let mut transaction = {
			let backend = test_trie();
			let mut cache = StorageTransactionCache::default();
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				&backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			ext.set_child_storage(&child_info_1, b"abc".to_vec(), b"def".to_vec());
			ext.set_child_storage(&child_info_2, b"abc".to_vec(), b"def".to_vec());
			ext.storage_root();
			cache.transaction.unwrap()
		};
		let mut duplicate = false;
		for (k, (value, rc)) in transaction.drain().iter() {
			// look for a key inserted twice: transaction rc is 2
			if *rc == 2 {
				duplicate = true;
				println!("test duplicate for {:?} {:?}", k, value);
			}
		}
		assert!(!duplicate);
	}

	#[test]
	fn set_storage_empty_allowed() {
		let initial: BTreeMap<_, _> = map![
			b"aaa".to_vec() => b"0".to_vec(),
			b"bbb".to_vec() => b"".to_vec()
		];
		let state = InMemoryBackend::<BlakeTwo256>::from(initial);
		let backend = state.as_trie_backend().unwrap();

		let mut overlay = OverlayedChanges::default();
		overlay.start_transaction();
		overlay.set_storage(b"ccc".to_vec(), Some(b"".to_vec()));
		assert_eq!(overlay.storage(b"ccc"), Some(Some(&[][..])));
		overlay.commit_transaction().unwrap();
		overlay.start_transaction();
		assert_eq!(overlay.storage(b"ccc"), Some(Some(&[][..])));
		assert_eq!(overlay.storage(b"bbb"), None);

		{
			let mut cache = StorageTransactionCache::default();
			let mut ext = Ext::new(
				&mut overlay,
				&mut cache,
				backend,
				changes_trie::disabled_state::<_, u64>(),
				None,
			);
			assert_eq!(ext.storage(b"bbb"), Some(vec![]));
			assert_eq!(ext.storage(b"ccc"), Some(vec![]));
			ext.clear_storage(b"ccc");
			assert_eq!(ext.storage(b"ccc"), None);
		}
		overlay.commit_transaction().unwrap();
		assert_eq!(overlay.storage(b"ccc"), Some(None));
	}

	#[test]
	fn runtime_registered_extensions_are_removed_after_execution() {
		use sp_externalities::ExternalitiesExt;
		sp_externalities::decl_extension! {
			struct DummyExt(u32);
		}

		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let wasm_code = RuntimeCode::empty();

		let mut state_machine = StateMachine::new(
			&backend,
			changes_trie::disabled_state::<_, u64>(),
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: false,
			},
			"test",
			&[],
			Default::default(),
			&wasm_code,
			TaskExecutor::new(),
		);

		let run_state_machine = |state_machine: &mut StateMachine<_, _, _, _>| {
			state_machine
				.execute_using_consensus_failure_handler::<fn(_, _) -> _, _, _>(
					ExecutionManager::NativeWhenPossible,
					Some(|| {
						sp_externalities::with_externalities(|mut ext| {
							ext.register_extension(DummyExt(2)).unwrap();
						})
						.unwrap();

						Ok(())
					}),
				)
				.unwrap();
		};

		run_state_machine(&mut state_machine);
		run_state_machine(&mut state_machine);
	}
}
