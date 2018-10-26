// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Substrate state machine implementation.
// end::description[]

#![warn(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[macro_use]
extern crate log;

extern crate hash_db;
extern crate substrate_trie;

extern crate parking_lot;
extern crate heapsize;
#[cfg_attr(test, macro_use)] extern crate substrate_primitives as primitives;
extern crate parity_codec as codec;
extern crate substrate_trie as trie;

use std::fmt;
use hash_db::Hasher;
use heapsize::HeapSizeOf;
use codec::Decode;
use primitives::storage::well_known_keys;

pub mod backend;
mod changes_trie;
mod ext;
mod testing;
mod overlayed_changes;
mod proving_backend;
mod trie_backend;
mod trie_backend_essence;

pub use trie::{TrieMut, TrieDBMut, DBValue, MemoryDB};
pub use testing::TestExternalities;
pub use ext::Ext;
pub use backend::Backend;
pub use changes_trie::{Storage as ChangesTrieStorage,
	RootsStorage as ChangesTrieRootsStorage,
	InMemoryStorage as InMemoryChangesTrieStorage,
	key_changes, key_changes_proof, key_changes_proof_check,
	prune as prune_changes_tries};
pub use overlayed_changes::OverlayedChanges;
pub use trie_backend_essence::Storage;
pub use trie_backend::TrieBackend;

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES :u64 = 1024;

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

/// Externalities: pinned to specific active address.
pub trait Externalities<H: Hasher> {
	/// Read storage of current contract being called.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Read child storage of current contract being called.
	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(&mut self, storage_key: Vec<u8>, key: Vec<u8>, value: Vec<u8>) -> bool {
		self.place_child_storage(storage_key, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(&mut self, storage_key: &[u8], key: &[u8]) -> bool {
		self.place_child_storage(storage_key.to_vec(), key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(&self, storage_key: &[u8], key: &[u8]) -> bool {
		self.child_storage(storage_key, key).is_some()
	}

	/// Clear an entire child storage.
	fn kill_child_storage(&mut self, storage_key: &[u8]);

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry. Return whether the operation succeeds.
	fn place_child_storage(&mut self, storage_key: Vec<u8>, key: Vec<u8>, value: Option<Vec<u8>>) -> bool;

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map. This will also update all child storage keys in the top-level storage map.
	fn storage_root(&mut self) -> H::Out where H::Out: Ord;

	/// Get the trie root of a child storage map. This will also update the value of the child storage keys in the top-level storage map. If the storage root equals default hash as defined by trie, the key in top-level storage map will be removed.
	///
	/// Returns None if key provided is not a storage key. This can due to not being started with CHILD_STORAGE_KEY_PREFIX, or the trie implementation regards the key as invalid.
	fn child_storage_root(&mut self, storage_key: &[u8]) -> Option<Vec<u8>>;

	/// Get the change trie root of the current storage overlay at given block.
	fn storage_changes_root(&mut self, block: u64) -> Option<H::Out> where H::Out: Ord;
}

/// Code execution engine.
pub trait CodeExecutor<H: Hasher>: Sized + Send + Sync {
	/// Externalities error type.
	type Error: Error;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<E: Externalities<H>>(
		&self,
		ext: &mut E,
		heap_pages: usize,
		code: &[u8],
		method: &str,
		data: &[u8],
		use_native: bool
	) -> (Result<Vec<u8>, Self::Error>, bool);
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
}

/// Like `ExecutionStrategy` only it also stores a handler in case of consensus failure.
pub enum ExecutionManager<F> {
	/// Execute with the native equivalent if it is compatible with the given wasm module; otherwise fall back to the wasm.
	NativeWhenPossible,
	/// Use the given wasm module.
	AlwaysWasm,
	/// Run with both the wasm and the native variant (if compatible). Call `F` in the case of any discrepency.
	Both(F),
}

impl<'a, F> From<&'a ExecutionManager<F>> for ExecutionStrategy {
	fn from(s: &'a ExecutionManager<F>) -> Self {
		match *s {
			ExecutionManager::NativeWhenPossible => ExecutionStrategy::NativeWhenPossible,
			ExecutionManager::AlwaysWasm => ExecutionStrategy::AlwaysWasm,
			ExecutionManager::Both(_) => ExecutionStrategy::Both,
		}
	}
}

/// Evaluate to ExecutionManager::NativeWhenPossible, without having to figure out the type.
pub fn native_when_possible<E>() -> ExecutionManager<fn(Result<Vec<u8>, E>, Result<Vec<u8>, E>)->Result<Vec<u8>, E>> {
	ExecutionManager::NativeWhenPossible
}

/// Evaluate to ExecutionManager::NativeWhenPossible, without having to figure out the type.
pub fn always_wasm<E>() -> ExecutionManager<fn(Result<Vec<u8>, E>, Result<Vec<u8>, E>)->Result<Vec<u8>, E>> {
	ExecutionManager::AlwaysWasm
}

/// Execute a call using the given state backend, overlayed changes, and call executor.
/// Produces a state-backend-specific "transaction" which can be used to apply the changes
/// to the backing store, such as the disk.
///
/// On an error, no prospective changes are written to the overlay.
///
/// Note: changes to code will be in place if this call is made again. For running partial
/// blocks (e.g. a transaction at a time), ensure a different method is used.
pub fn execute<H, B, T, Exec>(
	backend: &B,
	changes_trie_storage: Option<&T>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	strategy: ExecutionStrategy,
) -> Result<(Vec<u8>, B::Transaction, Option<MemoryDB<H>>), Box<Error>>
where
	H: Hasher,
	Exec: CodeExecutor<H>,
	B: Backend<H>,
	T: ChangesTrieStorage<H>,
	H::Out: Ord + HeapSizeOf,
{
	execute_using_consensus_failure_handler(
		backend,
		changes_trie_storage,
		overlay,
		exec,
		method,
		call_data,
		match strategy {
			ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm,
			ExecutionStrategy::NativeWhenPossible => ExecutionManager::NativeWhenPossible,
			ExecutionStrategy::Both => ExecutionManager::Both(|wasm_result, native_result| {
				warn!("Consensus error between wasm {:?} and native {:?}. Using wasm.", wasm_result, native_result);
				wasm_result
			}),
		},
	)
}

/// Execute a call using the given state backend, overlayed changes, and call executor.
/// Produces a state-backend-specific "transaction" which can be used to apply the changes
/// to the backing store, such as the disk.
///
/// On an error, no prospective changes are written to the overlay.
///
/// Note: changes to code will be in place if this call is made again. For running partial
/// blocks (e.g. a transaction at a time), ensure a different method is used.
pub fn execute_using_consensus_failure_handler<H, B, T, Exec, Handler>(
	backend: &B,
	changes_trie_storage: Option<&T>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	manager: ExecutionManager<Handler>,
) -> Result<(Vec<u8>, B::Transaction, Option<MemoryDB<H>>), Box<Error>>
where
	H: Hasher,
	Exec: CodeExecutor<H>,
	B: Backend<H>,
	T: ChangesTrieStorage<H>,
	H::Out: Ord + HeapSizeOf,
	Handler: FnOnce(Result<Vec<u8>, Exec::Error>, Result<Vec<u8>, Exec::Error>) -> Result<Vec<u8>, Exec::Error>
{
	let strategy: ExecutionStrategy = (&manager).into();

	// make a copy.
	let code = try_read_overlay_value(overlay, backend, well_known_keys::CODE)?
		.ok_or_else(|| Box::new(ExecutionError::CodeEntryDoesNotExist) as Box<Error>)?
		.to_vec();

	let heap_pages = try_read_overlay_value(overlay, backend, well_known_keys::HEAP_PAGES)?
		.and_then(|v| u64::decode(&mut &v[..])).unwrap_or(DEFAULT_HEAP_PAGES) as usize;

	// read changes trie configuration. The reason why we're doing it here instead of the
	// `OverlayedChanges` constructor is that we need proofs for this read as a part of
	// proof-of-execution on light clients. And the proof is recorded by the backend which
	// is created after OverlayedChanges

	let init_overlay = |overlay: &mut OverlayedChanges, final_check: bool| {
		let changes_trie_config = try_read_overlay_value(
			overlay,
			backend,
			well_known_keys::CHANGES_TRIE_CONFIG
		)?;
		set_changes_trie_config(overlay, changes_trie_config, final_check)
	};
	init_overlay(overlay, false)?;

	let result = {
		let mut orig_prospective = overlay.prospective.clone();

		let (result, was_native, storage_delta, changes_delta) = {
			let ((result, was_native), (storage_delta, changes_delta)) = {
				let mut externalities = ext::Ext::new(overlay, backend, changes_trie_storage);
				(
					exec.call(
						&mut externalities,
						heap_pages,
						&code,
						method,
						call_data,
						// attempt to run native first, if we're not directed to run wasm only
						strategy != ExecutionStrategy::AlwaysWasm,
					),
					externalities.transaction()
				)
			};
			(result, was_native, storage_delta, changes_delta)
		};

		// run wasm separately if we did run native the first time and we're meant to run both
		let (result, storage_delta, changes_delta) = if let (true, ExecutionManager::Both(on_consensus_failure)) =
			(was_native, manager)
		{
			overlay.prospective = orig_prospective.clone();

			let (wasm_result, wasm_storage_delta, wasm_changes_delta) = {
				let ((result, _), (storage_delta, changes_delta)) = {
					let mut externalities = ext::Ext::new(overlay, backend, changes_trie_storage);
					(
						exec.call(
							&mut externalities,
							heap_pages,
							&code,
							method,
							call_data,
							false,
						),
						externalities.transaction()
					)
				};
				(result, storage_delta, changes_delta)
			};

			if (result.is_ok() && wasm_result.is_ok() && result.as_ref().unwrap() == wasm_result.as_ref().unwrap()/* && delta == wasm_delta*/)
				|| (result.is_err() && wasm_result.is_err())
			{
				(result, storage_delta, changes_delta)
			} else {
				// Consensus error.
				(on_consensus_failure(wasm_result, result), wasm_storage_delta, wasm_changes_delta)
			}
		} else {
			(result, storage_delta, changes_delta)
		};
		result.map(move |out| (out, storage_delta, changes_delta))
	};

	// ensure that changes trie config has not been changed
	if result.is_ok() {
		init_overlay(overlay, true)?;
	}

	result.map_err(|e| Box::new(e) as _)
}

/// Prove execution using the given state backend, overlayed changes, and call executor.
/// Produces a state-backend-specific "transaction" which can be used to apply the changes
/// to the backing store, such as the disk.
/// Execution proof is the set of all 'touched' storage DBValues from the backend.
///
/// On an error, no prospective changes are written to the overlay.
///
/// Note: changes to code will be in place if this call is made again. For running partial
/// blocks (e.g. a transaction at a time), ensure a different method is used.
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
	H::Out: Ord + HeapSizeOf,
{
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>)?;
	let proving_backend = proving_backend::ProvingBackend::new(trie_backend);
	let (result, _, _) = execute::<H, _, changes_trie::InMemoryStorage<H>, _>(
		&proving_backend,
		None,
		overlay,
		exec,
		method,
		call_data,
		ExecutionStrategy::NativeWhenPossible
	)?;
	let proof = proving_backend.extract_proof();
	Ok((result, proof))
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
	H::Out: Ord + HeapSizeOf,
{
	let backend = proving_backend::create_proof_check_backend::<H>(root.into(), proof)?;
	execute::<H, _, changes_trie::InMemoryStorage<H>, _>(&backend, None, overlay, exec, method, call_data, ExecutionStrategy::NativeWhenPossible)
		.map(|(result, _, _)| result)
}

/// Generate storage read proof.
pub fn prove_read<B, H>(
	backend: B,
	key: &[u8]
) -> Result<(Option<Vec<u8>>, Vec<Vec<u8>>), Box<Error>>
where
	B: Backend<H>,
	H: Hasher,

	H::Out: Ord + HeapSizeOf
{
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>)?;
	let proving_backend = proving_backend::ProvingBackend::<_, H>::new(trie_backend);
	let result = proving_backend.storage(key).map_err(|e| Box::new(e) as Box<Error>)?;
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

	H::Out: Ord + HeapSizeOf
{
	let backend = proving_backend::create_proof_check_backend::<H>(root, proof)?;
	backend.storage(key).map_err(|e| Box::new(e) as Box<Error>)
}

/// Sets overlayed changes' changes trie configuration. Returns error if configuration
/// differs from previous OR config decode has failed.
pub(crate) fn set_changes_trie_config(overlay: &mut OverlayedChanges, config: Option<Vec<u8>>, final_check: bool) -> Result<(), Box<Error>> {
	let config = match config {
		Some(v) => Some(changes_trie::Configuration::decode(&mut &v[..])
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
	use codec::Encode;
	use overlayed_changes::OverlayedValue;
	use super::*;
	use super::backend::InMemory;
	use super::ext::Ext;
	use super::changes_trie::{
		InMemoryStorage as InMemoryChangesTrieStorage,
		Configuration as ChangesTrieConfig,
	};
	use primitives::{Blake2Hasher};

	struct DummyCodeExecutor {
		change_changes_trie_config: bool,
		native_available: bool,
		native_succeeds: bool,
		fallback_succeeds: bool,
	}

	impl<H: Hasher> CodeExecutor<H> for DummyCodeExecutor {
		type Error = u8;

		fn call<E: Externalities<H>>(
			&self,
			ext: &mut E,
			_heap_pages: usize,
			_code: &[u8],
			_method: &str,
			_data: &[u8],
			use_native: bool
		) -> (Result<Vec<u8>, Self::Error>, bool) {
			if self.change_changes_trie_config {
				ext.place_storage(well_known_keys::CHANGES_TRIE_CONFIG.to_vec(), Some(ChangesTrieConfig {
					digest_interval: 777,
					digest_levels: 333,
				}.encode()));
			}

			let using_native = use_native && self.native_available;
			match (using_native, self.native_succeeds, self.fallback_succeeds) {
				(true, true, _) | (false, _, true) =>
					(Ok(vec![ext.storage(b"value1").unwrap()[0] + ext.storage(b"value2").unwrap()[0]]), using_native),
				_ => (Err(0), using_native),
			}
		}
	}

	impl Error for u8 {}

	#[test]
	fn execute_works() {
		assert_eq!(execute(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			ExecutionStrategy::NativeWhenPossible
		).unwrap().0, vec![66]);
	}

	#[test]
	fn dual_execution_strategy_detects_consensus_failure() {
		let mut consensus_failed = false;
		assert!(execute_using_consensus_failure_handler(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: false,
				native_available: true,
				native_succeeds: true,
				fallback_succeeds: false,
			},
			"test",
			&[],
			ExecutionManager::Both(|we, _ne| {
				consensus_failed = true;
				println!("HELLO!");
				we
			}),
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
			let mut ext = Ext::new(&mut overlay, &backend, Some(&changes_trie_storage));
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
		let mut ext = Ext::new(&mut overlay, &backend, Some(&changes_trie_storage));

		assert!(ext.set_child_storage(b":child_storage:testchild".to_vec(), b"abc".to_vec(), b"def".to_vec()));
		assert_eq!(ext.child_storage(b":child_storage:testchild", b"abc"), Some(b"def".to_vec()));
		ext.kill_child_storage(b":child_storage:testchild");
		assert_eq!(ext.child_storage(b":child_storage:testchild", b"abc"), None);
	}

	#[test]
	fn prove_read_and_proof_check_works() {
		// fetch read proof from 'remote' full node
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let remote_proof = prove_read(remote_backend, b"value2").unwrap().1;
 		// check proof locally
		let local_result1 = read_proof_check::<Blake2Hasher>(remote_root, remote_proof.clone(), b"value2").unwrap();
		let local_result2 = read_proof_check::<Blake2Hasher>(remote_root, remote_proof.clone(), &[0xff]).is_ok();
 		// check that results are correct
		assert_eq!(local_result1, Some(vec![24]));
		assert_eq!(local_result2, false);
	}

	#[test]
	fn cannot_change_changes_trie_config() {
		assert!(execute(
			&trie_backend::tests::test_trie(),
			Some(&InMemoryChangesTrieStorage::new()),
			&mut Default::default(),
			&DummyCodeExecutor {
				change_changes_trie_config: true,
				native_available: false,
				native_succeeds: true,
				fallback_succeeds: true,
			},
			"test",
			&[],
			ExecutionStrategy::NativeWhenPossible
		).is_err());
	}
}
