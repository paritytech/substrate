// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! RPC API for GRANDPA.
#![warn(missing_docs)]

use futures::{FutureExt, TryFutureExt};
use jsonrpc_derive::rpc;
use std::fmt::Debug;
use finality_grandpa::BlockNumberOps;

mod serialized;

use sc_finality_grandpa::{SharedAuthoritySet, SharedVoterState};
use serialized::ReportedRoundStates;

/// Returned when Grandpa RPC endpoint is not ready.
pub const NOT_READY_ERROR_CODE: i64 = 1;

type FutureResult<T> =
	Box<dyn jsonrpc_core::futures::Future<Item = T, Error = jsonrpc_core::Error> + Send>;

#[derive(derive_more::Display, derive_more::From)]
/// Top-level error type for the RPC handler
pub enum Error {
	/// The GRANDPA RPC endpoint is not ready.
	#[display(fmt = "GRANDPA RPC endpoint not ready")]
	EndpointNotReady,
}

impl From<Error> for jsonrpc_core::Error {
	fn from(error: Error) -> Self {
		jsonrpc_core::Error {
			message: format!("{}", error).into(),
			code: jsonrpc_core::ErrorCode::ServerError(NOT_READY_ERROR_CODE),
			data: None,
		}
	}
}

/// Provides RPC methods for interacting with GRANDPA.
#[rpc]
pub trait GrandpaApi {
	/// Returns the state of the current best round state as well as the
	/// ongoing background rounds.
	#[rpc(name = "grandpa_roundState")]
	fn round_state(&self) -> FutureResult<ReportedRoundStates>;
}

/// Implements the GrandpaApi RPC trait for interacting with GRANDPA.
pub struct GrandpaRpcHandler<Hash, Block> {
	shared_voter_state: SharedVoterState,
	shared_authority_set: SharedAuthoritySet<Hash, Block>,
}

impl<Hash, Block> GrandpaRpcHandler<Hash, Block> {
	/// Creates a new GrandpaRpcHander instance.
	pub fn new(
		shared_voter_state: SharedVoterState,
		shared_authority_set: SharedAuthoritySet<Hash, Block>,
	) -> Self {
		Self {
			shared_voter_state,
			shared_authority_set,
		}
	}
}

impl<Hash, Block: Send + Sync> GrandpaApi for GrandpaRpcHandler<Hash, Block>
where
	Hash: Debug + Clone + Eq + Send + Sync + 'static,
	Block: BlockNumberOps + Send + Sync + 'static,
{
	fn round_state(&self) -> FutureResult<ReportedRoundStates> {
		let round_states =
			ReportedRoundStates::from(&self.shared_voter_state, &self.shared_authority_set);
		let future = async move { round_states }.boxed();
		Box::new(future.map_err(jsonrpc_core::Error::from).compat())
	}
}
