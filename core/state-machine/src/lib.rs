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

//! Substrate state machine implementation.

#![warn(missing_docs)]

use std::{fmt, panic::UnwindSafe, result, marker::PhantomData};
use std::borrow::Cow;
use log::warn;
use hash_db::Hasher;
use parity_codec::{Decode, Encode};
use primitives::{
	storage::well_known_keys, NativeOrEncoded, NeverNativeValue, OffchainExt
};

pub mod backend;
mod changes_trie;
mod ext;
mod testing;
mod basic;
mod overlayed_changes;
mod proving_backend;
mod trie_backend;
mod trie_backend_essence;

use overlayed_changes::OverlayedChangeSet;
pub use trie::{TrieMut, TrieDBMut, DBValue, MemoryDB};
pub use testing::TestExternalities;
pub use basic::BasicExternalities;
pub use ext::Ext;
pub use backend::Backend;
pub use changes_trie::{
	AnchorBlockId as ChangesTrieAnchorBlockId,
	Storage as ChangesTrieStorage,
	RootsStorage as ChangesTrieRootsStorage,
	InMemoryStorage as InMemoryChangesTrieStorage,
	key_changes, key_changes_proof, key_changes_proof_check,
	prune as prune_changes_tries,
	oldest_non_pruned_trie as oldest_non_pruned_changes_trie
};
pub use overlayed_changes::OverlayedChanges;
pub use proving_backend::{
	create_proof_check_backend, create_proof_check_backend_storage,
	Recorder as ProofRecorder, ProvingBackend,
};
pub use trie_backend_essence::{TrieBackendStorage, Storage};
pub use trie_backend::TrieBackend;

/// A wrapper around a child storage key.
///
/// This wrapper ensures that the child storage key is correct and properly used.  It is
/// impossible to create an instance of this struct without providing a correct `storage_key`.
pub struct ChildStorageKey<'a, H: Hasher> {
	storage_key: Cow<'a, [u8]>,
	_hasher: PhantomData<H>,
}

impl<'a, H: Hasher> ChildStorageKey<'a, H> {
	fn new(storage_key: Cow<'a, [u8]>) -> Option<Self> {
		if !trie::is_child_trie_key_valid::<H>(&storage_key) {
			return None;
		}

		Some(ChildStorageKey {
			storage_key,
			_hasher: PhantomData,
		})
	}

	/// Create a new `ChildStorageKey` from a vector.
	///
	/// `storage_key` has should start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_vec(key: Vec<u8>) -> Option<Self> {
		Self::new(Cow::Owned(key))
	}

	/// Create a new `ChildStorageKey` from a slice.
	///
	/// `storage_key` has should start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_slice(key: &'a [u8]) -> Option<Self> {
		Self::new(Cow::Borrowed(key))
	}

	/// Get access to the byte representation of the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn as_ref(&self) -> &[u8] {
		&*self.storage_key
	}

	/// Destruct this instance into an owned vector that represents the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn into_owned(self) -> Vec<u8> {
		self.storage_key.into_owned()
	}
}

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}

impl Error for ExecutionError {}

/// Externalities Error.
///
/// Externalities are not really allowed to have errors, since it's assumed that dependent code
/// would not be executed unless externalities were available. This is included for completeness,
/// and as a transition away from the pre-existing framework.
#[derive(Debug, Eq, PartialEq)]
pub enum ExecutionError {
	/// Backend error.
	Backend(String),
	/// The entry `:code` doesn't exist in storage so there's no way we can execute anything.
	CodeEntryDoesNotExist,
	/// Backend is incompatible with execution proof generation process.
	UnableToGenerateProof,
	/// Invalid execution proof.
	InvalidProof,
}

impl fmt::Display for ExecutionError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Externalities Error") }
}

type CallResult<R, E> = Result<NativeOrEncoded<R>, E>;

/// Externalities: pinned to specific active address.
pub trait Externalities<H: Hasher> {
	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash. This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		self.storage(key).map(|v| H::hash(&v))
	}

	/// Read original runtime storage, ignoring any overlayed changes.
	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get original storage value hash, ignoring any overlayed changes.
	/// This may be optimized for large values.
	fn original_storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		self.original_storage(key).map(|v| H::hash(&v))
	}

	/// Read child runtime storage.
	fn child_storage(&self, storage_key: ChildStorageKey<H>, key: &[u8]) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(&mut self, storage_key: ChildStorageKey<H>, key: Vec<u8>, value: Vec<u8>) {
		self.place_child_storage(storage_key, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(&mut self, storage_key: ChildStorageKey<H>, key: &[u8]) {
		self.place_child_storage(storage_key, key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(&self, storage_key: ChildStorageKey<H>, key: &[u8]) -> bool {
		self.child_storage(storage_key, key).is_some()
	}

	/// Clear an entire child storage.
	fn kill_child_storage(&mut self, storage_key: ChildStorageKey<H>);

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry. Return whether the operation succeeds.
	fn place_child_storage(&mut self, storage_key: ChildStorageKey<H>, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map. This will also update all child storage keys in the top-level storage map.
	fn storage_root(&mut self) -> H::Out where H::Out: Ord;

	/// Get the trie root of a child storage map. This will also update the value of the child
	/// storage keys in the top-level storage map.
	/// If the storage root equals the default hash as defined by the trie, the key in the top-level
	/// storage map will be removed.
	fn child_storage_root(&mut self, storage_key: ChildStorageKey<H>) -> Vec<u8>;

	/// Get the change trie root of the current storage overlay at a block with given parent.
	fn storage_changes_root(&mut self, parent: H::Out, parent_num: u64) -> Option<H::Out> where H::Out: Ord;

	/// Submit extrinsic.
	///
	/// Returns an error in case the API is not available.
	fn submit_extrinsic(&mut self, extrinsic: Vec<u8>) -> Result<(), ()>;
}

/// An implementation of offchain extensions that should never be triggered.
pub enum NeverOffchainExt {}

impl NeverOffchainExt {
	/// Create new offchain extensions.
	pub fn new<'a>() -> Option<&'a mut Self> {
		None
	}
}

impl OffchainExt for NeverOffchainExt {
	fn submit_extrinsic(&mut self, _extrinsic: Vec<u8>) { unreachable!() }
}

/// Code execution engine.
pub trait CodeExecutor<H: Hasher>: Sized + Send + Sync {
	/// Externalities error type.
	type Error: Error;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<
		E: Externalities<H>, R: Encode + Decode + PartialEq, NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe
	>(
		&self,
		ext: &mut E,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (CallResult<R, Self::Error>, bool);
}

/// Strategy for executing a call into the runtime.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ExecutionStrategy {
	/// Execute with the native equivalent if it is compatible with the given wasm module; otherwise fall back to the wasm.
	NativeWhenPossible,
	/// Use the given wasm module.
	AlwaysWasm,
	/// Run with both the wasm and the native variant (if compatible). Report any discrepency as an error.
	Both,
	/// First native, then if that fails or is not possible, wasm.
	NativeElseWasm,
}

type DefaultHandler<R, E> = fn(
	CallResult<R, E>,
	CallResult<R, E>,
) -> CallResult<R, E>;

/// Like `ExecutionStrategy` only it also stores a handler in case of consensus failure.
#[derive(Clone)]
pub enum ExecutionManager<F> {
	/// Execute with the native equivalent if it is compatible with the given wasm module; otherwise fall back to the wasm.
	NativeWhenPossible,
	/// Use the given wasm module.
	AlwaysWasm,
	/// Run with both the wasm and the native variant (if compatible). Call `F` in the case of any discrepency.
	Both(F),
	/// First native, then if that fails or is not possible, wasm.
	NativeElseWasm,
}

impl<'a, F> From<&'a ExecutionManager<F>> for ExecutionStrategy {
	fn from(s: &'a ExecutionManager<F>) -> Self {
		match *s {
			ExecutionManager::NativeWhenPossible => ExecutionStrategy::NativeWhenPossible,
			ExecutionManager::AlwaysWasm => ExecutionStrategy::AlwaysWasm,
			ExecutionManager::NativeElseWasm => ExecutionStrategy::NativeElseWasm,
			ExecutionManager::Both(_) => ExecutionStrategy::Both,
		}
	}
}

impl ExecutionStrategy {
	/// Gets the corresponding manager for the execution strategy.
	pub fn get_manager<E: std::fmt::Debug, R: Decode + Encode>(self) -> ExecutionManager<DefaultHandler<R, E>> {
		match self {
			ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm,
			ExecutionStrategy::NativeWhenPossible => ExecutionManager::NativeWhenPossible,
			ExecutionStrategy::NativeElseWasm => ExecutionManager::NativeElseWasm,
			ExecutionStrategy::Both => ExecutionManager::Both(|wasm_result, native_result| {
				warn!(
					"Consensus error between wasm {:?} and native {:?}. Using wasm.",
					wasm_result,
					native_result
				);
				wasm_result
			}),
		}
	}
}


/// Evaluate to ExecutionManager::NativeWhenPossible, without having to figure out the type.
pub fn native_when_possible<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	 ExecutionManager::NativeWhenPossible
}

/// Evaluate to ExecutionManager::NativeElseWasm, without having to figure out the type.
pub fn native_else_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	ExecutionManager::NativeElseWasm
}

/// Evaluate to ExecutionManager::NativeWhenPossible, without having to figure out the type.
pub fn always_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	ExecutionManager::AlwaysWasm
}

/// Creates new substrate state machine.
pub fn new<'a, H, B, T, O, Exec>(
	backend: &'a B,
	changes_trie_storage: Option<&'a T>,
	offchain_ext: Option<&'a mut O>,
	overlay: &'a mut OverlayedChanges,
	exec: &'a Exec,
	method: &'a str,
	call_data: &'a [u8],
) -> StateMachine<'a, H, B, T, O, Exec> {
	StateMachine {
		backend,
		changes_trie_storage,
		offchain_ext,
		overlay,
		exec,
		method,
		call_data,
		_hasher: PhantomData,
	}
}

/// The substrate state machine.
pub struct StateMachine<'a, H, B, T, O, Exec> {
	backend: &'a B,
	changes_trie_storage: Option<&'a T>,
	offchain_ext: Option<&'a mut O>,
	overlay: &'a mut OverlayedChanges,
	exec: &'a Exec,
	method: &'a str,
	call_data: &'a [u8],
	_hasher: PhantomData<H>,
}

impl<'a, H, B, T, O, Exec> StateMachine<'a, H, B, T, O, Exec> where
	H: Hasher,
	Exec: CodeExecutor<H>,
	B: Backend<H>,
	T: ChangesTrieStorage<H>,
	O: OffchainExt,
	H::Out: Ord,
{
	/// Execute a call using the given state backend, overlayed changes, and call executor.
	/// Produces a state-backend-specific "transaction" which can be used to apply the changes
	/// to the backing store, such as the disk.
	///
	/// On an error, no prospective changes are written to the overlay.
	///
	/// Note: changes to code will be in place if this call is made again. For running partial
	/// blocks (e.g. a transaction at a time), ensure a different method is used.
	pub fn execute(
		&mut self,
		strategy: ExecutionStrategy,
	) -> Result<(Vec<u8>, B::Transaction, Option<MemoryDB<H>>), Box<Error>> {
		// We are not giving a native call and thus we are sure that the result can never be a native
		// value.
		self.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			strategy.get_manager(),
			true,
			None,
		)
		.map(|(result, storage_tx, changes_tx)| (
			result.into_encoded(),
			storage_tx.expect("storage_tx is always computed when compute_tx is true; qed"),
			changes_tx,
		))
	}

	fn execute_aux<R, NC>(
		&mut self,
		compute_tx: bool,
		use_native: bool,
		native_call: Option<NC>,
	) -> (CallResult<R, Exec::Error>, bool, Option<B::Transaction>, Option<MemoryDB<H>>) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
	{
		let offchain = self.offchain_ext.as_mut();
		let mut externalities = ext::Ext::new(
			self.overlay,
			self.backend,
			self.changes_trie_storage,
			offchain.map(|x| &mut **x),
		);
		let (result, was_native) = self.exec.call(
			&mut externalities,
			self.method,
			self.call_data,
			use_native,
			native_call,
		);
		let (storage_delta, changes_delta) = if compute_tx {
			let (storage_delta, changes_delta) = externalities.transaction();
			(Some(storage_delta), changes_delta)
		} else {
			(None, None)
		};
		(result, was_native, storage_delta, changes_delta)
	}

	fn execute_call_with_both_strategy<Handler, R, NC>(
		&mut self,
		compute_tx: bool,
		mut native_call: Option<NC>,
		orig_prospective: OverlayedChangeSet,
		on_consensus_failure: Handler,
	) -> (CallResult<R, Exec::Error>, Option<B::Transaction>, Option<MemoryDB<H>>) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
		Handler: FnOnce(
			CallResult<R, Exec::Error>,
			CallResult<R, Exec::Error>
		) -> CallResult<R, Exec::Error>
	{
		let (result, was_native, storage_delta, changes_delta) = self.execute_aux(compute_tx, true, native_call.take());

		if was_native {
			self.overlay.prospective = orig_prospective.clone();
			let (wasm_result, _, wasm_storage_delta, wasm_changes_delta) = self.execute_aux(compute_tx, false, native_call);

			if (result.is_ok() && wasm_result.is_ok()
				&& result.as_ref().ok() == wasm_result.as_ref().ok())
				|| result.is_err() && wasm_result.is_err() {
				(result, storage_delta, changes_delta)
			} else {
				(on_consensus_failure(wasm_result, result), wasm_storage_delta, wasm_changes_delta)
			}
		} else {
			(result, storage_delta, changes_delta)
		}
	}

	fn execute_call_with_native_else_wasm_strategy<R, NC>(
		&mut self,
		compute_tx: bool,
		mut native_call: Option<NC>,
		orig_prospective: OverlayedChangeSet,
	) -> (CallResult<R, Exec::Error>, Option<B::Transaction>, Option<MemoryDB<H>>) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
	{
		let (result, was_native, storage_delta, changes_delta) = self.execute_aux(compute_tx, true, native_call.take());

		if !was_native || result.is_ok() {
			(result, storage_delta, changes_delta)
		} else {
			self.overlay.prospective = orig_prospective.clone();
			let (wasm_result, _, wasm_storage_delta, wasm_changes_delta) = self.execute_aux(compute_tx, false, native_call);
			(wasm_result, wasm_storage_delta, wasm_changes_delta)
		}
	}

	/// Execute a call using the given state backend, overlayed changes, and call executor.
	/// Produces a state-backend-specific "transaction" which can be used to apply the changes
	/// to the backing store, such as the disk.
	///
	/// On an error, no prospective changes are written to the overlay.
	///
	/// Note: changes to code will be in place if this call is made again. For running partial
	/// blocks (e.g. a transaction at a time), ensure a different method is used.
	pub fn execute_using_consensus_failure_handler<Handler, R, NC>(
		&mut self,
		manager: ExecutionManager<Handler>,
		compute_tx: bool,
		mut native_call: Option<NC>,
	) -> Result<(NativeOrEncoded<R>, Option<B::Transaction>, Option<MemoryDB<H>>), Box<Error>> where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
		Handler: FnOnce(
			CallResult<R, Exec::Error>,
			CallResult<R, Exec::Error>
		) -> CallResult<R, Exec::Error>
	{
		// read changes trie configuration. The reason why we're doing it here instead of the
		// `OverlayedChanges` constructor is that we need proofs for this read as a part of
		// proof-of-execution on light clients. And the proof is recorded by the backend which
		// is created after OverlayedChanges

		let backend = self.backend.clone();
		let init_overlay = |overlay: &mut OverlayedChanges, final_check: bool| {
			let changes_trie_config = try_read_overlay_value(
				overlay,
				backend,
				well_known_keys::CHANGES_TRIE_CONFIG
			)?;
			set_changes_trie_config(overlay, changes_trie_config, final_check)
		};
		init_overlay(self.overlay, false)?;

		let result = {
			let orig_prospective = self.overlay.prospective.clone();

			let (result, storage_delta, changes_delta) = match manager {
				ExecutionManager::Both(on_consensus_failure) => {
					self.execute_call_with_both_strategy(compute_tx, native_call.take(), orig_prospective, on_consensus_failure)
				},
				ExecutionManager::NativeElseWasm => {
					self.execute_call_with_native_else_wasm_strategy(compute_tx, native_call.take(), orig_prospective)
				},
				ExecutionManager::AlwaysWasm => {
					let (result, _, storage_delta, changes_delta) = self.execute_aux(compute_tx, false, native_call);
					(result, storage_delta, changes_delta)
				},
				ExecutionManager::NativeWhenPossible => {
					let (result, _was_native, storage_delta, changes_delta) = self.execute_aux(compute_tx, true, native_call);
					(result, storage_delta, changes_delta)
				},
			};
			result.map(move |out| (out, storage_delta, changes_delta))
		};

		if result.is_ok() {
			init_overlay(self.overlay, true)?;
		}

		result.map_err(|e| Box::new(e) as _)
	}
}

/// Prove execution using the given state backend, overlayed changes, and call executor.
pub fn prove_execution<B, H, Exec>(
	backend: B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<(Vec<u8>, Vec<Vec<u8>>), Box<Error>>
where
	B: Backend<H>,
	H: Hasher,
	Exec: CodeExecutor<H>,
	H::Out: Ord,
{
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>)?;
	prove_execution_on_trie_backend(&trie_backend, overlay, exec, method, call_data)
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
pub fn prove_execution_on_trie_backend<S, H, Exec>(
	trie_backend: &TrieBackend<S, H>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<(Vec<u8>, Vec<Vec<u8>>), Box<Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher,
	Exec: CodeExecutor<H>,
	H::Out: Ord,
{
	let proving_backend = proving_backend::ProvingBackend::new(trie_backend);
	let mut sm = StateMachine {
		backend: &proving_backend,
		changes_trie_storage: None as Option<&changes_trie::InMemoryStorage<H>>,
		offchain_ext: NeverOffchainExt::new(),
		overlay,
		exec,
		method,
		call_data,
		_hasher: PhantomData,
	};
	let (result, _, _) = sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
		native_else_wasm(),
		false,
		None,
	)?;
	let proof = proving_backend.extract_proof();
	Ok((result.into_encoded(), proof))
}

/// Check execution proof, generated by `prove_execution` call.
pub fn execution_proof_check<H, Exec>(
	root: H::Out,
	proof: Vec<Vec<u8>>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<Vec<u8>, Box<Error>>
where
	H: Hasher,
	Exec: CodeExecutor<H>,
	H::Out: Ord,
{
	let trie_backend = create_proof_check_backend::<H>(root.into(), proof)?;
	execution_proof_check_on_trie_backend(&trie_backend, overlay, exec, method, call_data)
}

/// Check execution proof on proving backend, generated by `prove_execution` call.
pub fn execution_proof_check_on_trie_backend<H, Exec>(
	trie_backend: &TrieBackend<MemoryDB<H>, H>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<Vec<u8>, Box<Error>>
where
	H: Hasher,
	Exec: CodeExecutor<H>,
	H::Out: Ord,
{
	let mut sm = StateMachine {
		backend: trie_backend,
		changes_trie_storage: None as Option<&changes_trie::InMemoryStorage<H>>,
		offchain_ext: NeverOffchainExt::new(),
		overlay,
		exec,
		method,
		call_data,
		_hasher: PhantomData,
	};
	sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
		native_else_wasm(),
		false,
		None,
	).map(|(result, _, _)| result.into_encoded())
}

/// Generate storage read proof.
pub fn prove_read<B, H>(
	backend: B,
	key: &[u8]
) -> Result<(Option<Vec<u8>>, Vec<Vec<u8>>), Box<Error>>
where
	B: Backend<H>,
	H: Hasher,
	H::Out: Ord
{
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(
			||Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>
		)?;
	prove_read_on_trie_backend(&trie_backend, key)
}

/// Generate child storage read proof.
pub fn prove_child_read<B, H>(
	backend: B,
	storage_key: &[u8],
	key: &[u8],
) -> Result<(Option<Vec<u8>>, Vec<Vec<u8>>), Box<Error>>
where
	B: Backend<H>,
	H: Hasher,
	H::Out: Ord
{
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>)?;
	prove_child_read_on_trie_backend(&trie_backend, storage_key, key)
}


/// Generate storage read proof on pre-created trie backend.
pub fn prove_read_on_trie_backend<S, H>(
	trie_backend: &TrieBackend<S, H>,
	key: &[u8]
) -> Result<(Option<Vec<u8>>, Vec<Vec<u8>>), Box<Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher,
	H::Out: Ord
{
	let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
	let result = proving_backend.storage(key).map_err(|e| Box::new(e) as Box<Error>)?;
	Ok((result, proving_backend.extract_proof()))
}

/// Generate storage read proof on pre-created trie backend.
pub fn prove_child_read_on_trie_backend<S, H>(
	trie_backend: &TrieBackend<S, H>,
	storage_key: &[u8],
	key: &[u8]
) -> Result<(Option<Vec<u8>>, Vec<Vec<u8>>), Box<Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher,
	H::Out: Ord
{
	let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
	let result = proving_backend.child_storage(storage_key, key)
		.map_err(|e| Box::new(e) as Box<Error>)?;
	Ok((result, proving_backend.extract_proof()))
}

/// Check storage read proof, generated by `prove_read` call.
pub fn read_proof_check<H>(
	root: H::Out,
	proof: Vec<Vec<u8>>,
	key: &[u8],
) -> Result<Option<Vec<u8>>, Box<Error>>
where
	H: Hasher,
	H::Out: Ord
{
	let proving_backend = create_proof_check_backend::<H>(root, proof)?;
	read_proof_check_on_proving_backend(&proving_backend, key)
}

/// Check child storage read proof, generated by `prove_child_read` call.
pub fn read_child_proof_check<H>(
	root: H::Out,
	proof: Vec<Vec<u8>>,
	storage_key: &[u8],
	key: &[u8],
) -> Result<Option<Vec<u8>>, Box<Error>>
where
	H: Hasher,
	H::Out: Ord
{
	let proving_backend = create_proof_check_backend::<H>(root, proof)?;
	read_child_proof_check_on_proving_backend(&proving_backend, storage_key, key)
}


/// Check storage read proof on pre-created proving backend.
pub fn read_proof_check_on_proving_backend<H>(
	proving_backend: &TrieBackend<MemoryDB<H>, H>,
	key: &[u8],
) -> Result<Option<Vec<u8>>, Box<Error>>
where
	H: Hasher,
	H::Out: Ord
{
	proving_backend.storage(key).map_err(|e| Box::new(e) as Box<Error>)
}

/// Check child storage read proof on pre-created proving backend.
pub fn read_child_proof_check_on_proving_backend<H>(
	proving_backend: &TrieBackend<MemoryDB<H>, H>,
	storage_key: &[u8],
	key: &[u8],
) -> Result<Option<Vec<u8>>, Box<Error>>
where
	H: Hasher,
	H::Out: Ord
{
	proving_backend.child_storage(storage_key, key).map_err(|e| Box::new(e) as Box<Error>)
}

/// Sets overlayed changes' changes trie configuration. Returns error if configuration
/// differs from previous OR config decode has failed.
pub(crate) fn set_changes_trie_config(overlay: &mut OverlayedChanges, config: Option<Vec<u8>>, final_check: bool) -> Result<(), Box<Error>> {
	let config = match config {
		Some(v) => Some(Decode::decode(&mut &v[..])
			.ok_or_else(|| Box::new("Failed to decode changes trie configuration".to_owned()) as Box<Error>)?),
		None => None,
	};

	if final_check && overlay.changes_trie_config.is_some() != config.is_some() {
		return Err(Box::new("Changes trie configuration change is not supported".to_owned()));
	}

	if let Some(config) = config {
		if !overlay.set_changes_trie_config(config) {
			return Err(Box::new("Changes trie configuration change is not supported".to_owned()));
		}
	}
	Ok(())
}

/// Reads storage value from overlay or from the backend.
fn try_read_overlay_value<H, B>(overlay: &OverlayedChanges, backend: &B, key: &[u8])
	-> Result<Option<Vec<u8>>, Box<Error>>
where
	H: Hasher,

	B: Backend<H>,
{
	match overlay.storage(key).map(|x| x.map(|x| x.to_vec())) {
		Some(value) => Ok(value),
		None => backend.storage(key)
			.map_err(|err| Box::new(ExecutionError::Backend(format!("{}", err))) as Box<Error>),
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use parity_codec::Encode;
	use overlayed_changes::OverlayedValue;
	use super::*;
	use super::backend::InMemory;
	use super::ext::Ext;
	use super::changes_trie::{
		InMemoryStorage as InMemoryChangesTrieStorage,
		Configuration as ChangesTrieConfig,
	};
	use primitives::{Blake2Hasher, map};

	struct DummyCodeExecutor {
		change_changes_trie_config: bool,
		native_available: bool,
		native_succeeds: bool,
		fallback_succeeds: bool,
	}

	impl<H: Hasher> CodeExecutor<H> for DummyCodeExecutor {
		type Error = u8;

		fn call<E: Externalities<H>, R: Encode + Decode + PartialEq, NC: FnOnce() -> result::Result<R, &'static str>>(
			&self,
			ext: &mut E,
			_method: &str,
			_data: &[u8],
			use_native: bool,
			_native_call: Option<NC>,
		) -> (CallResult<R, Self::Error>, bool) {
			if self.change_changes_trie_config {
				ext.place_storage(
					well_known_keys::CHANGES_TRIE_CONFIG.to_vec(),
					Some(
						ChangesTrieConfig {
							digest_interval: 777,
							digest_levels: 333,
						}.encode()
					)
				);
			}

			let using_native = use_native && self.native_available;
			match (using_native, self.native_succeeds, self.fallback_succeeds) {
				(true, true, _) | (false, _, true) => {
					(
						Ok(
							NativeOrEncoded::Encoded(
								vec![
									ext.storage(b"value1").unwrap()[0] +
									ext.storage(b"value2").unwrap()[0]
								]
							)
						),
						using_native
					)
				},
				_ => (Err(0), using_native),
			}
		}
	}

	impl Error for u8 {}

	#[test]
	fn execute_works() {
		assert_eq!(new(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			NeverOffchainExt::new(),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
		).execute(
			ExecutionStrategy::NativeWhenPossible
		).unwrap().0, vec![66]);
	}


	#[test]
	fn execute_works_with_native_else_wasm() {
		assert_eq!(new(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			NeverOffchainExt::new(),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
		).execute(
			ExecutionStrategy::NativeElseWasm
		).unwrap().0, vec![66]);
	}

	#[test]
	fn dual_execution_strategy_detects_consensus_failure() {
		let mut consensus_failed = false;
		assert!(new(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			NeverOffchainExt::new(),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: false,
			},
			"test",
			&[],
		).execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
			ExecutionManager::Both(|we, _ne| {
				consensus_failed = true;
				println!("HELLO!");
				we
			}),
			true,
			None,
		).is_err());
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
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let (remote_result, remote_proof) = prove_execution(remote_backend,
			&mut Default::default(), &executor, "test", &[]).unwrap();

		// check proof locally
		let local_result = execution_proof_check::<Blake2Hasher, _>(remote_root, remote_proof,
			&mut Default::default(), &executor, "test", &[]).unwrap();

		// check that both results are correct
		assert_eq!(remote_result, vec![66]);
		assert_eq!(remote_result, local_result);
	}

	#[test]
	fn clear_prefix_in_ext_works() {
		let initial: HashMap<_, _> = map![
			b"aaa".to_vec() => b"0".to_vec(),
			b"abb".to_vec() => b"1".to_vec(),
			b"abc".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"3".to_vec()
		];
		let backend = InMemory::<Blake2Hasher>::from(initial).try_into_trie_backend().unwrap();
		let mut overlay = OverlayedChanges {
			committed: map![
				b"aba".to_vec() => OverlayedValue::from(Some(b"1312".to_vec())),
				b"bab".to_vec() => OverlayedValue::from(Some(b"228".to_vec()))
			],
			prospective: map![
				b"abd".to_vec() => OverlayedValue::from(Some(b"69".to_vec())),
				b"bbd".to_vec() => OverlayedValue::from(Some(b"42".to_vec()))
			],
			..Default::default()
		};

		{
			let changes_trie_storage = InMemoryChangesTrieStorage::new();
			let mut ext = Ext::new(&mut overlay, &backend, Some(&changes_trie_storage), NeverOffchainExt::new());
			ext.clear_prefix(b"ab");
		}
		overlay.commit_prospective();

		assert_eq!(
			overlay.committed,
			map![
				b"abc".to_vec() => None.into(),
				b"abb".to_vec() => None.into(),
				b"aba".to_vec() => None.into(),
				b"abd".to_vec() => None.into(),

				b"bab".to_vec() => Some(b"228".to_vec()).into(),
				b"bbd".to_vec() => Some(b"42".to_vec()).into()
			],
		);
	}

	#[test]
	fn set_child_storage_works() {
		let backend = InMemory::<Blake2Hasher>::default().try_into_trie_backend().unwrap();
		let changes_trie_storage = InMemoryChangesTrieStorage::new();
		let mut overlay = OverlayedChanges::default();
		let mut ext = Ext::new(
			&mut overlay,
			&backend,
			Some(&changes_trie_storage),
			NeverOffchainExt::new()
		);

		ext.set_child_storage(
			ChildStorageKey::from_slice(b":child_storage:default:testchild").unwrap(),
			b"abc".to_vec(),
			b"def".to_vec()
		);
		assert_eq!(
			ext.child_storage(
				ChildStorageKey::from_slice(b":child_storage:default:testchild").unwrap(),
				b"abc"
			),
			Some(b"def".to_vec())
		);
		ext.kill_child_storage(
			ChildStorageKey::from_slice(b":child_storage:default:testchild").unwrap()
		);
		assert_eq!(
			ext.child_storage(
				ChildStorageKey::from_slice(b":child_storage:default:testchild").unwrap(),
				b"abc"
			),
			None
		);
	}

	#[test]
	fn prove_read_and_proof_check_works() {
		// fetch read proof from 'remote' full node
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let remote_proof = prove_read(remote_backend, b"value2").unwrap().1;
 		// check proof locally
		let local_result1 = read_proof_check::<Blake2Hasher>(
			remote_root,
			remote_proof.clone(),
			b"value2"
		).unwrap();
		let local_result2 = read_proof_check::<Blake2Hasher>(
			remote_root,
			remote_proof.clone(),
			&[0xff]
		).is_ok();
 		// check that results are correct
		assert_eq!(local_result1, Some(vec![24]));
		assert_eq!(local_result2, false);
		// on child trie
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let remote_proof = prove_child_read(
			remote_backend,
			b":child_storage:default:sub1",
			b"value3"
		).unwrap().1;
		let local_result1 = read_child_proof_check::<Blake2Hasher>(
			remote_root,
			remote_proof.clone(),
			b":child_storage:default:sub1",b"value3"
		).unwrap();
		let local_result2 = read_child_proof_check::<Blake2Hasher>(
			remote_root,
			remote_proof.clone(),
			b":child_storage:default:sub1",
			b"value2"
		).unwrap();
		assert_eq!(local_result1, Some(vec![142]));
		assert_eq!(local_result2, None);
	}

	#[test]
	fn cannot_change_changes_trie_config() {
		assert!(new(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			NeverOffchainExt::new(),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: true,
				native_available: false,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
		).execute(
			ExecutionStrategy::NativeWhenPossible
		).is_err());
	}

	#[test]
	fn cannot_change_changes_trie_config_with_native_else_wasm() {
		assert!(new(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			NeverOffchainExt::new(),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: true,
				native_available: false,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
		).execute(
			ExecutionStrategy::NativeElseWasm
		).is_err());
	}
}
