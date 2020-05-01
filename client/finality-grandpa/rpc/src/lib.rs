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

mod error;
mod report;

use report::{ReportAuthoritySet, ReportVoterState, ReportedRoundStates};

/// Returned when Grandpa RPC endpoint is not ready.
pub const NOT_READY_ERROR_CODE: i64 = 1;

type FutureResult<T> =
	Box<dyn jsonrpc_core::futures::Future<Item = T, Error = jsonrpc_core::Error> + Send>;

/// Provides RPC methods for interacting with GRANDPA.
#[rpc]
pub trait GrandpaApi {
	/// Returns the state of the current best round state as well as the
	/// ongoing background rounds.
	#[rpc(name = "grandpa_roundState")]
	fn round_state(&self) -> FutureResult<ReportedRoundStates>;
}

/// Implements the GrandpaApi RPC trait for interacting with GRANDPA.
pub struct GrandpaRpcHandler<AuthoritySet, VoterState> {
	authority_set: AuthoritySet,
	voter_state: VoterState,
}

impl<AuthoritySet, VoterState> GrandpaRpcHandler<AuthoritySet, VoterState> {
	/// Creates a new GrandpaRpcHander instance.
	pub fn new(authority_set: AuthoritySet, voter_state: VoterState) -> Self {
		Self {
			authority_set,
			voter_state,
		}
	}
}

impl<AuthoritySet, VoterState> GrandpaApi for GrandpaRpcHandler<AuthoritySet, VoterState>
where
	VoterState: ReportVoterState + Send + Sync + 'static,
	AuthoritySet: ReportAuthoritySet + Send + Sync + 'static,
{
	fn round_state(&self) -> FutureResult<ReportedRoundStates> {
		let round_states = ReportedRoundStates::from(&self.authority_set, &self.voter_state);
		let future = async move { round_states }.boxed();
		Box::new(future.map_err(jsonrpc_core::Error::from).compat())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use jsonrpc_core::IoHandler;

	#[test]
	fn create_grandpa_rpc_handler() {
		// let shared_voter_state = SharedVoterState::empty();
		// let shared_authority_set = example_shared_authority_set();

		// let handler = GrandpaRpcHandler::new(shared_voter_state, shared_authority_set);
		// let mut io = IoHandler::new();
		// io.extend_with(GrandpaApi::to_delegate(handler));

		// let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		// let response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"GRANDPA RPC endpoint not ready"},"id":1}"#;

		// assert_eq!(Some(response.into()), io.handle_request_sync(request));
	}
}
