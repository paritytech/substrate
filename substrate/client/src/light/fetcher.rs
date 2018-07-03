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

//! Light client data fetcher. Fetches requested data from remote full nodes.

use std::sync::Arc;
use futures::IntoFuture;

use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT};
use state_machine::CodeExecutor;

use call_executor::CallResult;
use error::{Error as ClientError, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::call_executor::check_execution_proof;

/// Remote call request.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest<Hash: ::std::fmt::Display> {
	/// Call at state of given block.
	pub block: Hash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher<Block: BlockT>: Send + Sync {
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=ClientError>;

	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<Block::Hash>) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker<Block: BlockT>: Send + Sync {
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult>;
}

/// Remote data checker.
pub struct LightDataChecker<S, E, F> {
	blockchain: Arc<Blockchain<S, F>>,
	executor: E,
}

impl<S, E, F> LightDataChecker<S, E, F> {
	/// Create new light data checker.
	pub fn new(blockchain: Arc<Blockchain<S, F>>, executor: E) -> Self {
		Self {
			blockchain,
			executor,
		}
	}

	/// Get blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}
}

impl<S, E, F, Block> FetchChecker<Block> for LightDataChecker<S, E, F>
	where
		Block: BlockT,
		<Block as BlockT>::Hash: From<[u8; 32]> + Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
		<<Block as BlockT>::Header as HeaderT>::Number: As<u32>,
		S: BlockchainStorage<Block>,
		E: CodeExecutor,
		F: Fetcher<Block>,
{
	fn check_execution_proof(&self, request: &RemoteCallRequest<Block::Hash>, remote_proof: Vec<Vec<u8>>) -> ClientResult<CallResult> {
		check_execution_proof(&*self.blockchain, &self.executor, request, remote_proof)
	}
}
