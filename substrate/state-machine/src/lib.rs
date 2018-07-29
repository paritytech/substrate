// Copyright 2017 Parity Technologies (UK) Ltd.
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

#[cfg_attr(test, macro_use)]
extern crate hex_literal;

#[macro_use]
extern crate log;

extern crate ethereum_types;
extern crate hashdb;
extern crate memorydb;
extern crate triehash;
extern crate patricia_trie;

extern crate byteorder;
extern crate parking_lot;

use std::collections::HashMap;
use std::collections::hash_map::Drain;
use std::fmt;

pub mod backend;
mod ext;
mod testing;
mod proving_backend;
mod trie_backend;

pub use testing::TestExternalities;
pub use ext::Ext;
pub use backend::Backend;
pub use trie_backend::{TryIntoTrieBackend, TrieBackend, TrieH256, Storage, DBValue};

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	prospective: HashMap<Vec<u8>, Option<Vec<u8>>>,
	committed: HashMap<Vec<u8>, Option<Vec<u8>>>,
}

impl OverlayedChanges {
	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.prospective.get(key)
			.or_else(|| self.committed.get(key))
			.map(|x| x.as_ref().map(AsRef::as_ref))
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		self.prospective.insert(key, val);
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	fn clear_prefix(&mut self, prefix: &[u8]) {
		// Iterate over all prospective and mark all keys that share
		// the given prefix as removed (None).
		for (key, value) in self.prospective.iter_mut() {
			if key.starts_with(prefix) {
				*value = None;
			}
		}

		// Then do the same with keys from commited changes.
		// NOTE that we are making changes in the prospective change set.
		for key in self.committed.keys() {
			if key.starts_with(prefix) {
				self.prospective.insert(key.to_owned(), None);
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			::std::mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			self.committed.extend(self.prospective.drain());
		}
	}

	/// Drain prospective changes to an iterator.
	pub fn drain(&mut self) -> Drain<Vec<u8>, Option<Vec<u8>>> {
		self.committed.drain()
	}
}

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {
	/// Error implies execution should be retried.
	fn needs_retry(&self) -> bool { false }
}

impl Error for ExecutionError {}

/// Externalities Error.
///
/// Externalities are not really allowed to have errors, since it's assumed that dependent code
/// would not be executed unless externalities were available. This is included for completeness,
/// and as a transition away from the pre-existing framework.
#[derive(Debug, Eq, PartialEq)]
pub enum ExecutionError {
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
pub trait Externalities {
	/// Read storage of current contract being called.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map.
	fn storage_root(&mut self) -> [u8; 32];
}

/// Code execution engine.
pub trait CodeExecutor: Sized + Send + Sync {
	/// Externalities error type.
	type Error: Error;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<E: Externalities>(
		&self,
		ext: &mut E,
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
pub fn execute<B: backend::Backend, Exec: CodeExecutor>(
	backend: &B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	strategy: ExecutionStrategy,
) -> Result<(Vec<u8>, B::Transaction), Box<Error>> {
	execute_using_consensus_failure_handler(
		backend,
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
pub fn execute_using_consensus_failure_handler<
	B: backend::Backend,
	Exec: CodeExecutor,
	Handler: FnOnce(Result<Vec<u8>, Exec::Error>, Result<Vec<u8>, Exec::Error>) -> Result<Vec<u8>, Exec::Error>
>(
	backend: &B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
	manager: ExecutionManager<Handler>,
) -> Result<(Vec<u8>, B::Transaction), Box<Error>> {
	let strategy: ExecutionStrategy = (&manager).into();

	// make a copy.
	let code = ext::Ext::new(overlay, backend).storage(b":code")
		.ok_or_else(|| Box::new(ExecutionError::CodeEntryDoesNotExist) as Box<Error>)?
		.to_vec();

	let result = {
		let mut orig_prospective = overlay.prospective.clone();

		let (result, was_native, delta) = loop {
			let ((result, was_native), delta) = {
				let mut externalities = ext::Ext::new(overlay, backend);
				(
					exec.call(
						&mut externalities,
						&code,
						method,
						call_data,
						// attempt to run native first, if we're not directed to run wasm only
						strategy != ExecutionStrategy::AlwaysWasm,
					),
					externalities.transaction()
				)
			};

			if result.as_ref().err().map_or(false, |e| e.needs_retry()) {
				overlay.prospective = orig_prospective.clone();
			} else {
				break (result, was_native, delta)
			}
		};

		// run wasm separately if we did run native the first time and we're meant to run both
		let (result, delta) = if let (true, ExecutionManager::Both(on_consensus_failure)) =
			(was_native, manager)
		{
			overlay.prospective = orig_prospective.clone();

			let (wasm_result, wasm_delta) = loop {
				let ((result, _), delta) = {
					let mut externalities = ext::Ext::new(overlay, backend);
					(
						exec.call(
							&mut externalities,
							&code,
							method,
							call_data,
							false,
						),
						externalities.transaction()
					)
				};

				if result.as_ref().err().map_or(false, |e| e.needs_retry()) {
					overlay.prospective = orig_prospective.clone();
				} else {
					break (result, delta)
				}
			};

			if (result.is_ok() && wasm_result.is_ok() && result.as_ref().unwrap() == wasm_result.as_ref().unwrap()/* && delta == wasm_delta*/)
				|| (result.is_err() && wasm_result.is_err() && format!("{}", result.as_ref().unwrap_err()) == format!("{}", wasm_result.as_ref().unwrap_err()))
			{
				(result, delta)
			} else {
				// Consensus error.
				(on_consensus_failure(wasm_result, result), wasm_delta)
			}
		} else {
			(result, delta)
		};
		result.map(move |out| (out, delta))
	};

	match result {
		Ok(x) => {
			Ok(x)
		}
		Err(e) => {
			Err(Box::new(e))
		}
	}
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
pub fn prove_execution<B: TryIntoTrieBackend, Exec: CodeExecutor>(
	backend: B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<(Vec<u8>, Vec<Vec<u8>>, <TrieBackend as Backend>::Transaction), Box<Error>> {
	let trie_backend = backend.try_into_trie_backend()
		.ok_or_else(|| Box::new(ExecutionError::UnableToGenerateProof) as Box<Error>)?;
	let proving_backend = proving_backend::ProvingBackend::new(trie_backend);
	let (result, transaction) = execute(&proving_backend, overlay, exec, method, call_data, ExecutionStrategy::NativeWhenPossible)?;
	let proof = proving_backend.extract_proof();
	Ok((result, proof, transaction))
}

/// Check execution proof, generated by `prove_execution` call.
pub fn execution_proof_check<Exec: CodeExecutor>(
	root: [u8; 32],
	proof: Vec<Vec<u8>>,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<(Vec<u8>, memorydb::MemoryDB), Box<Error>> {
	let backend = proving_backend::create_proof_check_backend(root.into(), proof)?;
	execute(&backend, overlay, exec, method, call_data, ExecutionStrategy::NativeWhenPossible)
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::backend::InMemory;
	use super::ext::Ext;

	struct DummyCodeExecutor {
		native_available: bool,
		native_succeeds: bool,
		fallback_succeeds: bool,
	}

	impl CodeExecutor for DummyCodeExecutor {
		type Error = u8;

		fn call<E: Externalities>(
			&self,
			ext: &mut E,
			_code: &[u8],
			_method: &str,
			_data: &[u8],
			use_native: bool
		) -> (Result<Vec<u8>, Self::Error>, bool) {
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
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: HashMap<_, _> = map![
			b"doe".to_vec() => b"reindeer".to_vec(),
			b"dog".to_vec() => b"puppyXXX".to_vec(),
			b"dogglesworth".to_vec() => b"catXXX".to_vec(),
			b"doug".to_vec() => b"notadog".to_vec()
		];
		let backend = InMemory::from(initial);
		let mut overlay = OverlayedChanges {
			committed: map![
				b"dog".to_vec() => Some(b"puppy".to_vec()),
				b"dogglesworth".to_vec() => Some(b"catYYY".to_vec()),
				b"doug".to_vec() => Some(vec![])
			],
			prospective: map![
				b"dogglesworth".to_vec() => Some(b"cat".to_vec()),
				b"doug".to_vec() => None
			],
		};
		let mut ext = Ext::new(&mut overlay, &backend);
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), ROOT);
	}

	#[test]
	fn execute_works() {
		assert_eq!(execute(
			&trie_backend::tests::test_trie(),
			&mut Default::default(),
			&DummyCodeExecutor {
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
			&mut Default::default(),
			&DummyCodeExecutor {
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
			native_available: true,
			native_succeeds: true,
			fallback_succeeds: true,
		};

		// fetch execution proof from 'remote' full node
		let remote_backend = trie_backend::tests::test_trie();
		let remote_root = remote_backend.storage_root(::std::iter::empty()).0;
		let (remote_result, remote_proof, _) = prove_execution(remote_backend,
			&mut Default::default(), &executor, "test", &[]).unwrap();

		// check proof locally
		let (local_result, _) = execution_proof_check(remote_root, remote_proof,
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
		let backend = InMemory::from(initial).try_into_trie_backend().unwrap();
		let mut overlay = OverlayedChanges {
			committed: map![
				b"aba".to_vec() => Some(b"1312".to_vec()),
				b"bab".to_vec() => Some(b"228".to_vec())
			],
			prospective: map![
				b"abd".to_vec() => Some(b"69".to_vec()),
				b"bbd".to_vec() => Some(b"42".to_vec())
			],
		};

		{
			let mut ext = Ext::new(&mut overlay, &backend);
			ext.clear_prefix(b"ab");
		}
		overlay.commit_prospective();

		assert_eq!(
			overlay.committed,
			map![
				b"abb".to_vec() => None,
				b"abc".to_vec() => None,
				b"aba".to_vec() => None,
				b"abd".to_vec() => None,

				b"bab".to_vec() => Some(b"228".to_vec()),
				b"bbd".to_vec() => Some(b"42".to_vec())
			],
		);
	}
}
