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

use std::{fmt, result, collections::HashMap, panic::UnwindSafe, marker::PhantomData};
use log::{warn, trace};
use hash_db::Hasher;
use codec::{Decode, Encode};
use primitives::{
	storage::well_known_keys, NativeOrEncoded, NeverNativeValue, offchain::OffchainExt,
	traits::{KeystoreExt, CodeExecutor}, hexdisplay::HexDisplay, hash::H256,
};
use overlayed_changes::OverlayedChangeSet;
use externalities::Extensions;

pub mod backend;
mod changes_trie;
mod error;
mod ext;
mod testing;
mod basic;
mod overlayed_changes;
mod proving_backend;
mod trie_backend;
mod trie_backend_essence;

pub use trie::{trie_types::{Layout, TrieDBMut}, TrieMut, DBValue, MemoryDB};
pub use testing::TestExternalities;
pub use basic::BasicExternalities;
pub use ext::Ext;
pub use backend::Backend;
pub use changes_trie::{
	AnchorBlockId as ChangesTrieAnchorBlockId,
	Storage as ChangesTrieStorage,
	RootsStorage as ChangesTrieRootsStorage,
	InMemoryStorage as InMemoryChangesTrieStorage,
	BuildCache as ChangesTrieBuildCache,
	CacheAction as ChangesTrieCacheAction,
	ConfigurationRange as ChangesTrieConfigurationRange,
	key_changes, key_changes_proof, key_changes_proof_check,
	prune as prune_changes_tries,
	oldest_non_pruned_trie as oldest_non_pruned_changes_trie,
};
pub use overlayed_changes::OverlayedChanges;
pub use proving_backend::{
	create_proof_check_backend, create_proof_check_backend_storage, merge_storage_proofs,
	ProofRecorder, ProvingBackend, ProvingBackendRecorder, StorageProof,
};
pub use trie_backend_essence::{TrieBackendStorage, Storage};
pub use trie_backend::TrieBackend;
pub use error::{Error, ExecutionError};

type CallResult<R, E> = Result<NativeOrEncoded<R>, E>;

type DefaultHandler<R, E> = fn(CallResult<R, E>, CallResult<R, E>) -> CallResult<R, E>;

/// Type of changes trie transaction.
pub type ChangesTrieTransaction<H, N> = (
	MemoryDB<H>,
	ChangesTrieCacheAction<<H as Hasher>::Out, N>,
);

/// Strategy for executing a call into the runtime.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ExecutionStrategy {
	/// Execute with the native equivalent if it is compatible with the given wasm module; otherwise fall back to the wasm.
	NativeWhenPossible,
	/// Use the given wasm module.
	AlwaysWasm,
	/// Run with both the wasm and the native variant (if compatible). Report any discrepancy as an error.
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
	/// Execute with the native equivalent if it is compatible with the given wasm module; otherwise fall back to the wasm.
	NativeWhenPossible,
	/// Use the given wasm module. The backend on which code is executed code could be
	/// trusted to provide all storage or not (i.e. the light client cannot be trusted to provide
	/// for all storage queries since the storage entries it has come from an external node).
	AlwaysWasm(BackendTrustLevel),
	/// Run with both the wasm and the native variant (if compatible). Call `F` in the case of any discrepancy.
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
			ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm(BackendTrustLevel::Trusted),
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

/// Evaluate to ExecutionManager::NativeElseWasm, without having to figure out the type.
pub fn native_else_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	ExecutionManager::NativeElseWasm
}

/// Evaluate to ExecutionManager::AlwaysWasm with trusted backend, without having to figure out the type.
fn always_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	ExecutionManager::AlwaysWasm(BackendTrustLevel::Trusted)
}

/// Evaluate ExecutionManager::AlwaysWasm with untrusted backend, without having to figure out the type.
fn always_untrusted_wasm<E, R: Decode>() -> ExecutionManager<DefaultHandler<R, E>> {
	ExecutionManager::AlwaysWasm(BackendTrustLevel::Untrusted)
}

/// The substrate state machine.
pub struct StateMachine<'a, B, H, N, T, Exec> where H: Hasher<Out=H256>, B: Backend<H> {
	backend: &'a B,
	exec: &'a Exec,
	method: &'a str,
	call_data: &'a [u8],
	overlay: &'a mut OverlayedChanges,
	extensions: Extensions,
	changes_trie_storage: Option<&'a T>,
	_marker: PhantomData<(H, N)>,
}

impl<'a, B, H, N, T, Exec> StateMachine<'a, B, H, N, T, Exec> where
	H: Hasher<Out=H256>,
	Exec: CodeExecutor,
	B: Backend<H>,
	T: ChangesTrieStorage<H, N>,
	N: crate::changes_trie::BlockNumber,
{
	/// Creates new substrate state machine.
	pub fn new(
		backend: &'a B,
		changes_trie_storage: Option<&'a T>,
		offchain_ext: Option<OffchainExt>,
		overlay: &'a mut OverlayedChanges,
		exec: &'a Exec,
		method: &'a str,
		call_data: &'a [u8],
		keystore: Option<KeystoreExt>,
	) -> Self {
		let mut extensions = Extensions::new();

		if let Some(keystore) = keystore {
			extensions.register(keystore);
		}

		if let Some(offchain) = offchain_ext {
			extensions.register(offchain);
		}

		Self {
			backend,
			exec,
			method,
			call_data,
			extensions,
			overlay,
			changes_trie_storage,
			_marker: PhantomData,
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
	pub fn execute(&mut self, strategy: ExecutionStrategy) -> Result<
		(Vec<u8>, (B::Transaction, H::Out), Option<ChangesTrieTransaction<H, N>>),
		Box<dyn Error>,
	> {
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
	) -> (
		CallResult<R, Exec::Error>,
		bool,
		Option<(B::Transaction, H::Out)>,
		Option<ChangesTrieTransaction<H, N>>,
	) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	{
		let mut ext = Ext::new(
			self.overlay,
			self.backend,
			self.changes_trie_storage.clone(),
			Some(&mut self.extensions),
		);

		let id = ext.id;
		trace!(
			target: "state-trace", "{:04x}: Call {} at {:?}. Input={:?}",
			id,
			self.method,
			self.backend,
			HexDisplay::from(&self.call_data),
		);

		let (result, was_native) = self.exec.call(
			&mut ext,
			self.method,
			self.call_data,
			use_native,
			native_call,
		);

		let (storage_delta, changes_delta) = if compute_tx {
			let (storage_delta, changes_delta) = ext.transaction();
			(Some(storage_delta), changes_delta)
		} else {
			(None, None)
		};

		trace!(
			target: "state-trace", "{:04x}: Return. Native={:?}, Result={:?}",
			id,
			was_native,
			result,
		);

		(result, was_native, storage_delta, changes_delta)
	}

	fn execute_call_with_both_strategy<Handler, R, NC>(
		&mut self,
		compute_tx: bool,
		mut native_call: Option<NC>,
		orig_prospective: OverlayedChangeSet,
		on_consensus_failure: Handler,
	) -> (
		CallResult<R, Exec::Error>,
		Option<(B::Transaction, H::Out)>,
		Option<ChangesTrieTransaction<H, N>>,
	) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		Handler: FnOnce(
			CallResult<R, Exec::Error>,
			CallResult<R, Exec::Error>,
		) -> CallResult<R, Exec::Error>
	{
		let (result, was_native, storage_delta, changes_delta) = self.execute_aux(
			compute_tx,
			true,
			native_call.take(),
		);

		if was_native {
			self.overlay.prospective = orig_prospective.clone();
			let (wasm_result, _, wasm_storage_delta, wasm_changes_delta) = self.execute_aux(
				compute_tx,
				false,
				native_call,
			);

			if (result.is_ok() && wasm_result.is_ok()
				&& result.as_ref().ok() == wasm_result.as_ref().ok())
				|| result.is_err() && wasm_result.is_err()
			{
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
	) -> (
		CallResult<R, Exec::Error>,
		Option<(B::Transaction, H::Out)>,
		Option<ChangesTrieTransaction<H, N>>,
	) where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	{
		let (result, was_native, storage_delta, changes_delta) = self.execute_aux(
			compute_tx,
			true,
			native_call.take(),
		);

		if !was_native || result.is_ok() {
			(result, storage_delta, changes_delta)
		} else {
			self.overlay.prospective = orig_prospective.clone();
			let (wasm_result, _, wasm_storage_delta, wasm_changes_delta) = self.execute_aux(
				compute_tx,
				false,
				native_call,
			);
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
	) -> Result<(
		NativeOrEncoded<R>,
		Option<(B::Transaction, H::Out)>,
		Option<ChangesTrieTransaction<H, N>>,
	), Box<dyn Error>> where
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		Handler: FnOnce(
			CallResult<R, Exec::Error>,
			CallResult<R, Exec::Error>,
		) -> CallResult<R, Exec::Error>
	{
		// read changes trie configuration. The reason why we're doing it here instead of the
		// `OverlayedChanges` constructor is that we need proofs for this read as a part of
		// proof-of-execution on light clients. And the proof is recorded by the backend which
		// is created after OverlayedChanges

		let init_overlay = |overlay: &mut OverlayedChanges, final_check: bool, backend: &B| {
			let changes_trie_config = try_read_overlay_value(
				overlay,
				backend,
				well_known_keys::CHANGES_TRIE_CONFIG
			)?;
			set_changes_trie_config(overlay, changes_trie_config, final_check)
		};
		init_overlay(self.overlay, false, &self.backend)?;

		let result = {
			let orig_prospective = self.overlay.prospective.clone();

			let (result, storage_delta, changes_delta) = match manager {
				ExecutionManager::Both(on_consensus_failure) => {
					self.execute_call_with_both_strategy(
						compute_tx,
						native_call.take(),
						orig_prospective,
						on_consensus_failure,
					)
				},
				ExecutionManager::NativeElseWasm => {
					self.execute_call_with_native_else_wasm_strategy(
						compute_tx,
						native_call.take(),
						orig_prospective,
					)
				},
				ExecutionManager::AlwaysWasm(trust_level) => {
					let _abort_guard = match trust_level {
						BackendTrustLevel::Trusted => None,
						BackendTrustLevel::Untrusted => Some(panic_handler::AbortGuard::never_abort()),
					};
					let res = self.execute_aux(compute_tx, false, native_call);
					(res.0, res.2, res.3)
				},
				ExecutionManager::NativeWhenPossible => {
					let res = self.execute_aux(compute_tx, true, native_call);
					(res.0, res.2, res.3)
				},
			};
			result.map(move |out| (out, storage_delta, changes_delta))
		};

		if result.is_ok() {
			init_overlay(self.overlay, true, self.backend)?;
		}

		result.map_err(|e| Box::new(e) as _)
	}
}

/// Prove execution using the given state backend, overlayed changes, and call executor.
pub fn prove_execution<B, H, Exec>(
	mut backend: B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	keystore: Option<KeystoreExt>,
) -> Result<(Vec<u8>, StorageProof), Box<dyn Error>>
where
	B: Backend<H>,
	H: Hasher<Out=H256>,
	Exec: CodeExecutor,
{
	let trie_backend = backend.as_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
	prove_execution_on_trie_backend(trie_backend, overlay, exec, method, call_data, keystore)
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
	keystore: Option<KeystoreExt>,
) -> Result<(Vec<u8>, StorageProof), Box<dyn Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher<Out=H256>,
	Exec: CodeExecutor,
{
	let proving_backend = proving_backend::ProvingBackend::new(trie_backend);
	let mut sm = StateMachine::<_, H, _, InMemoryChangesTrieStorage<H, u64>, Exec>::new(
		&proving_backend, None, None, overlay, exec, method, call_data, keystore,
	);

	let (result, _, _) = sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
		always_wasm(),
		false,
		None,
	)?;
	let proof = sm.backend.extract_proof();
	Ok((result.into_encoded(), proof))
}

/// Check execution proof, generated by `prove_execution` call.
pub fn execution_proof_check<H, Exec>(
	root: H::Out,
	proof: StorageProof,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	keystore: Option<KeystoreExt>,
) -> Result<Vec<u8>, Box<dyn Error>>
where
	H: Hasher<Out=H256>,
	Exec: CodeExecutor,
	H::Out: Ord + 'static,
{
	let trie_backend = create_proof_check_backend::<H>(root.into(), proof)?;
	execution_proof_check_on_trie_backend(&trie_backend, overlay, exec, method, call_data, keystore)
}

/// Check execution proof on proving backend, generated by `prove_execution` call.
pub fn execution_proof_check_on_trie_backend<H, Exec>(
	trie_backend: &TrieBackend<MemoryDB<H>, H>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	keystore: Option<KeystoreExt>,
) -> Result<Vec<u8>, Box<dyn Error>>
where
	H: Hasher<Out=H256>,
	Exec: CodeExecutor,
{
	let mut sm = StateMachine::<_, H, _, InMemoryChangesTrieStorage<H, u64>, Exec>::new(
		trie_backend, None, None, overlay, exec, method, call_data, keystore,
	);

	sm.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
		always_untrusted_wasm(),
		false,
		None,
	).map(|(result, _, _)| result.into_encoded())
}

/// Generate storage read proof.
pub fn prove_read<B, H, I>(
	mut backend: B,
	keys: I,
) -> Result<StorageProof, Box<dyn Error>>
where
	B: Backend<H>,
	H: Hasher<Out=H256>,
	H::Out: Ord,
	I: IntoIterator,
	I::Item: AsRef<[u8]>,
{
	let trie_backend = backend.as_trie_backend()
		.ok_or_else(
			|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>
		)?;
	prove_read_on_trie_backend(trie_backend, keys)
}

/// Generate child storage read proof.
pub fn prove_child_read<B, H, I>(
	mut backend: B,
	storage_key: &[u8],
	keys: I,
) -> Result<StorageProof, Box<dyn Error>>
where
	B: Backend<H>,
	H: Hasher,
	H::Out: Ord,
	I: IntoIterator,
	I::Item: AsRef<[u8]>,
{
	let trie_backend = backend.as_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<dyn Error>)?;
	prove_child_read_on_trie_backend(trie_backend, storage_key, keys)
}

/// Generate storage read proof on pre-created trie backend.
pub fn prove_read_on_trie_backend<S, H, I>(
	trie_backend: &TrieBackend<S, H>,
	keys: I,
) -> Result<StorageProof, Box<dyn Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher,
	H::Out: Ord,
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
	storage_key: &[u8],
	keys: I,
) -> Result<StorageProof, Box<dyn Error>>
where
	S: trie_backend_essence::TrieBackendStorage<H>,
	H: Hasher,
	H::Out: Ord,
	I: IntoIterator,
	I::Item: AsRef<[u8]>,
{
	let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
	for key in keys.into_iter() {
		proving_backend
			.child_storage(storage_key, key.as_ref())
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
	H::Out: Ord,
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

/// Check child storage read proof, generated by `prove_child_read` call.
pub fn read_child_proof_check<H, I>(
	root: H::Out,
	proof: StorageProof,
	storage_key: &[u8],
	keys: I,
) -> Result<HashMap<Vec<u8>, Option<Vec<u8>>>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Ord,
	I: IntoIterator,
	I::Item: AsRef<[u8]>,
{
	let proving_backend = create_proof_check_backend::<H>(root, proof)?;
	let mut result = HashMap::new();
	for key in keys.into_iter() {
		let value = read_child_proof_check_on_proving_backend(
			&proving_backend,
			storage_key,
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
	H::Out: Ord,
{
	proving_backend.storage(key).map_err(|e| Box::new(e) as Box<dyn Error>)
}

/// Check child storage read proof on pre-created proving backend.
pub fn read_child_proof_check_on_proving_backend<H>(
	proving_backend: &TrieBackend<MemoryDB<H>, H>,
	storage_key: &[u8],
	key: &[u8],
) -> Result<Option<Vec<u8>>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Ord,
{
	proving_backend.child_storage(storage_key, key).map_err(|e| Box::new(e) as Box<dyn Error>)
}

/// Sets overlayed changes' changes trie configuration. Returns error if configuration
/// differs from previous OR config decode has failed.
fn set_changes_trie_config(
	overlay: &mut OverlayedChanges,
	config: Option<Vec<u8>>,
	final_check: bool,
) -> Result<(), Box<dyn Error>> {
	let config = match config {
		Some(v) => Some(Decode::decode(&mut &v[..])
			.map_err(|_| Box::new("Failed to decode changes trie configuration".to_owned()) as Box<dyn Error>)?),
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
fn try_read_overlay_value<H, B>(
	overlay: &OverlayedChanges,
	backend: &B, key: &[u8],
) -> Result<Option<Vec<u8>>, Box<dyn Error>> where H: Hasher, B: Backend<H> {
	match overlay.storage(key).map(|x| x.map(|x| x.to_vec())) {
		Some(value) => Ok(value),
		None => backend
			.storage(key)
			.map_err(|err| Box::new(ExecutionError::Backend(format!("{}", err))) as Box<dyn Error>),
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use codec::Encode;
	use overlayed_changes::OverlayedValue;
	use super::*;
	use super::backend::InMemory;
	use super::ext::Ext;
	use super::changes_trie::{
		InMemoryStorage as InMemoryChangesTrieStorage,
		Configuration as ChangesTrieConfig,
	};
	use primitives::{Blake2Hasher, map, traits::Externalities, storage::ChildStorageKey};

	struct DummyCodeExecutor {
		change_changes_trie_config: bool,
		native_available: bool,
		native_succeeds: bool,
		fallback_succeeds: bool,
	}

	impl CodeExecutor for DummyCodeExecutor {
		type Error = u8;

		fn call<
			E: Externalities,
			R: Encode + Decode + PartialEq,
			NC: FnOnce() -> result::Result<R, String>,
		>(
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

	#[test]
	fn execute_works() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();

		let mut state_machine = StateMachine::new(
			&backend,
			Some(&changes_trie_storage),
			None,
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			None,
		);

		assert_eq!(
			state_machine.execute(ExecutionStrategy::NativeWhenPossible).unwrap().0,
			vec![66],
		);
	}


	#[test]
	fn execute_works_with_native_else_wasm() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();

		let mut state_machine = StateMachine::new(
			&backend,
			Some(&changes_trie_storage),
			None,
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			None,
		);

		assert_eq!(state_machine.execute(ExecutionStrategy::NativeElseWasm).unwrap().0, vec![66]);
	}

	#[test]
	fn dual_execution_strategy_detects_consensus_failure() {
		let mut consensus_failed = false;
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();

		let mut state_machine = StateMachine::new(
			&backend,
			Some(&changes_trie_storage),
			None,
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: false,
			},
			"test",
			&[],
			None,
		);

		assert!(
			state_machine.execute_using_consensus_failure_handler::<_, NeverNativeValue, fn() -> _>(
				ExecutionManager::Both(|we, _ne| {
					consensus_failed = true;
					we
				}),
				true,
				None,
			).is_err()
		);
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
		let remote_root = remote_backend.storage_root(std::iter::empty()).0;
		let (remote_result, remote_proof) = prove_execution(
			remote_backend,
			&mut Default::default(),
			&executor,
			"test",
			&[],
			None,
		).unwrap();

		// check proof locally
		let local_result = execution_proof_check::<Blake2Hasher, _>(
			remote_root,
			remote_proof,
			&mut Default::default(),
			&executor,
			"test",
			&[],
			None,
		).unwrap();

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
		let mut state = InMemory::<Blake2Hasher>::from(initial);
		let backend = state.as_trie_backend().unwrap();
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
			let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
			let mut ext = Ext::new(
				&mut overlay,
				backend,
				Some(&changes_trie_storage),
				None,
			);
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
		let mut state = InMemory::<Blake2Hasher>::default();
		let backend = state.as_trie_backend().unwrap();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
		let mut overlay = OverlayedChanges::default();
		let mut ext = Ext::new(
			&mut overlay,
			backend,
			Some(&changes_trie_storage),
			None,
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
		let remote_proof = prove_read(remote_backend, &[b"value2"]).unwrap();
 		// check proof locally
		let local_result1 = read_proof_check::<Blake2Hasher, _>(
			remote_root,
			remote_proof.clone(),
			&[b"value2"],
		).unwrap();
		let local_result2 = read_proof_check::<Blake2Hasher, _>(
			remote_root,
			remote_proof.clone(),
			&[&[0xff]],
		).is_ok();
 		// check that results are correct
		assert_eq!(
			local_result1.into_iter().collect::<Vec<_>>(),
			vec![(b"value2".to_vec(), Some(vec![24]))],
		);
		assert_eq!(local_result2, false);
		// on child trie
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let remote_proof = prove_child_read(
			remote_backend,
			b":child_storage:default:sub1",
			&[b"value3"],
		).unwrap();
		let local_result1 = read_child_proof_check::<Blake2Hasher, _>(
			remote_root,
			remote_proof.clone(),
			b":child_storage:default:sub1",
			&[b"value3"],
		).unwrap();
		let local_result2 = read_child_proof_check::<Blake2Hasher, _>(
			remote_root,
			remote_proof.clone(),
			b":child_storage:default:sub1",
			&[b"value2"],
		).unwrap();
		assert_eq!(
			local_result1.into_iter().collect::<Vec<_>>(),
			vec![(b"value3".to_vec(), Some(vec![142]))],
		);
		assert_eq!(
			local_result2.into_iter().collect::<Vec<_>>(),
			vec![(b"value2".to_vec(), None)],
		);
	}

	#[test]
	fn cannot_change_changes_trie_config() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();

		let mut state_machine = StateMachine::new(
			&backend,
			Some(&changes_trie_storage),
			None,
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: true,
				native_available: false,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			None,
		);

		assert!(state_machine.execute(ExecutionStrategy::NativeWhenPossible).is_err());
	}

	#[test]
	fn cannot_change_changes_trie_config_with_native_else_wasm() {
		let backend = trie_backend::tests::test_trie();
		let mut overlayed_changes = Default::default();
		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();

		let mut state_machine = StateMachine::new(
			&backend,
			Some(&changes_trie_storage),
			None,
			&mut overlayed_changes,
			&DummyCodeExecutor {
				change_changes_trie_config: true,
				native_available: false,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			None,
		);

		assert!(state_machine.execute(ExecutionStrategy::NativeElseWasm).is_err());
	}
}
