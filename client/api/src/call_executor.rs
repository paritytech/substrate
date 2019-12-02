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

//! A method call executor interface.

use std::{cmp::Ord, panic::UnwindSafe, result, cell::RefCell};
use codec::{Encode, Decode};
use sp_runtime::{
	generic::BlockId, traits::Block as BlockT, traits::NumberFor,
};
use state_machine::{
	self, OverlayedChanges, ExecutionManager, ExecutionStrategy,
	ChangesTrieTransaction, StorageProof,
};
use executor::{RuntimeVersion, NativeVersion};
use externalities::Extensions;
use hash_db::Hasher;
use primitives::{Blake2Hasher, NativeOrEncoded};

use sp_api::{ProofRecorder, InitializeBlock};
use sp_blockchain;

/// Method call executor.
pub trait CallExecutor<B, H>
where
	B: BlockT,
	H: Hasher<Out=B::Hash>,
	H::Out: Ord,
{
	/// Externalities error type.
	type Error: state_machine::Error;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(
		&self,
		id: &BlockId<B>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		extensions: Option<Extensions>,
	) -> Result<Vec<u8>, sp_blockchain::Error>;

	/// Execute a contextual call on top of state in a block of a given hash.
	///
	/// No changes are made.
	/// Before executing the method, passed header is installed as the current header
	/// of the execution context.
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
		at: &BlockId<B>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		initialize_block: InitializeBlock<'a, B>,
		execution_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		proof_recorder: &Option<ProofRecorder<B>>,
		extensions: Option<Extensions>,
	) -> sp_blockchain::Result<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone;

	/// Extract RuntimeVersion of given block
	///
	/// No changes are made.
	fn runtime_version(&self, id: &BlockId<B>) -> Result<RuntimeVersion, sp_blockchain::Error>;

	/// Execute a call to a contract on top of given state.
	///
	/// No changes are made.
	fn call_at_state<
		S: state_machine::Backend<H>,
		F: FnOnce(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>,
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(&self,
		state: &S,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8],
		manager: ExecutionManager<F>,
		native_call: Option<NC>,
		extensions: Option<Extensions>,
	) -> Result<
		(
			NativeOrEncoded<R>,
			(S::Transaction, H::Out),
			Option<ChangesTrieTransaction<Blake2Hasher, NumberFor<B>>>
		),
		sp_blockchain::Error,
	>;

	/// Execute a call to a contract on top of given state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_state<S: state_machine::Backend<H>>(
		&self,
		mut state: S,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, StorageProof), sp_blockchain::Error> {
		let trie_state = state.as_trie_backend()
			.ok_or_else(||
				Box::new(state_machine::ExecutionError::UnableToGenerateProof)
					as Box<dyn state_machine::Error>
			)?;
		self.prove_at_trie_state(trie_state, overlay, method, call_data)
	}

	/// Execute a call to a contract on top of given trie state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_trie_state<S: state_machine::TrieBackendStorage<H>>(
		&self,
		trie_state: &state_machine::TrieBackend<S, H>,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, StorageProof), sp_blockchain::Error>;

	/// Get runtime version if supported.
	fn native_runtime_version(&self) -> Option<&NativeVersion>;
}
