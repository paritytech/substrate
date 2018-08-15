// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use std::sync::Arc;
use std::cmp::Ord;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::Block as BlockT;
use state_machine::{self, OverlayedChanges, Ext,
	CodeExecutor, ExecutionManager, native_when_possible};
use runtime_io::Externalities;
use executor::{RuntimeVersion, RuntimeInfo};
use patricia_trie::NodeCodec;
use primitives::{KeccakHasher, RlpCodec};
use hashdb::Hasher;
use rlp::Encodable;

use backend;
use error;

/// Information regarding the result of a call.
#[derive(Debug, Clone)]
pub struct CallResult {
	/// The data that was returned from the call.
	pub return_data: Vec<u8>,
	/// The changes made to the state by the call.
	pub changes: OverlayedChanges,
}

/// Method call executor.
pub trait CallExecutor<B, H, C>
where
	B: BlockT,
	H: Hasher,
	H::Out: Ord + Encodable,
	C: NodeCodec<H>,
{
	/// Externalities error type.
	type Error: state_machine::Error;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(&self,
		id: &BlockId<B>,
		method: &str,
		call_data: &[u8],
	) -> Result<CallResult, error::Error>;

	/// Extract RuntimeVersion of given block
	///
	/// No changes are made.
	fn runtime_version(&self, id: &BlockId<B>) -> Result<RuntimeVersion, error::Error>;

	/// Execute a call to a contract on top of given state.
	///
	/// No changes are made.
	fn call_at_state<
		S: state_machine::Backend<H, C>,
		F: FnOnce(Result<Vec<u8>, Self::Error>, Result<Vec<u8>, Self::Error>) -> Result<Vec<u8>, Self::Error>,
	>(&self,
		state: &S,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8],
		manager: ExecutionManager<F>
	) -> Result<(Vec<u8>, S::Transaction), error::Error>;

	/// Execute a call to a contract on top of given state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_state<S: state_machine::Backend<H, C>>(&self,
		state: S,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error>;

	/// Get runtime version if supported.
	fn native_runtime_version(&self) -> Option<RuntimeVersion>;
}

/// Call executor that executes methods locally, querying all required
/// data from local backend.
pub struct LocalCallExecutor<B, E> {
	backend: Arc<B>,
	executor: E,
}

impl<B, E> LocalCallExecutor<B, E> {
	/// Creates new instance of local call executor.
	pub fn new(backend: Arc<B>, executor: E) -> Self {
		LocalCallExecutor { backend, executor }
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

impl<B, E, Block> CallExecutor<Block, KeccakHasher, RlpCodec> for LocalCallExecutor<B, E>
where
	B: backend::LocalBackend<Block, KeccakHasher, RlpCodec>,
	E: CodeExecutor<KeccakHasher> + RuntimeInfo,
	Block: BlockT,
{
	type Error = E::Error;

	fn call(&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8],
	) -> error::Result<CallResult> {
		let mut changes = OverlayedChanges::default();
		let (return_data, _) = self.call_at_state(
			&self.backend.state_at(*id)?,
			&mut changes,
			method,
			call_data,
			native_when_possible(),
		)?;
		Ok(CallResult{ return_data, changes })
	}

	fn runtime_version(&self, id: &BlockId<Block>) -> error::Result<RuntimeVersion> {
		let mut overlay = OverlayedChanges::default();
		let state = self.backend.state_at(*id)?;
		let mut externalities = Ext::new(&mut overlay, &state);
		let code = externalities.storage(b":code").ok_or(error::ErrorKind::VersionInvalid)?
			.to_vec();

		self.executor.runtime_version(&mut externalities, &code)
			.ok_or(error::ErrorKind::VersionInvalid.into())
	}

	fn call_at_state<
		S: state_machine::Backend<KeccakHasher, RlpCodec>,
		F: FnOnce(Result<Vec<u8>, Self::Error>, Result<Vec<u8>, Self::Error>) -> Result<Vec<u8>, Self::Error>,
	>(&self,
		state: &S,
		changes: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8],
		manager: ExecutionManager<F>,
	) -> error::Result<(Vec<u8>, S::Transaction)> {
		state_machine::execute_using_consensus_failure_handler(
			state,
			changes,
			&self.executor,
			method,
			call_data,
			manager,
		).map_err(Into::into)
	}

	fn prove_at_state<S: state_machine::Backend<KeccakHasher, RlpCodec>>(&self,
		state: S,
		changes: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, Vec<Vec<u8>>), error::Error> {
		state_machine::prove_execution(
			state,
			changes,
			&self.executor,
			method,
			call_data,
		)
		.map(|(result, proof, _)| (result, proof))
		.map_err(Into::into)
	}

	fn native_runtime_version(&self) -> Option<RuntimeVersion> {
		<E as RuntimeInfo>::NATIVE_VERSION
	}
}
