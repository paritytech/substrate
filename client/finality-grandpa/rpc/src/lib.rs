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

use futures::{FutureExt, TryFutureExt};
use jsonrpc_derive::rpc;
use jsonrpc_core::Error;
use sc_finality_grandpa::{SharedVoterState, SharedAuthoritySet, AuthorityId, voter};
use finality_grandpa::BlockNumberOps;
use serde::{Serialize, Deserialize};
use std::{collections::HashSet, fmt::Debug};

type FutureResult<T> = Box<dyn jsonrpc_core::futures::Future<Item = T, Error = Error> + Send>;

#[rpc]
pub trait GrandpaApi {
	#[rpc(name = "grandpa_roundState")]
	fn grandpa_round_state(&self) -> FutureResult<RoundState>;
}

pub struct GrandpaRpcHandler<Hash, Block> {
	// WIP: pass AuthorityId as type parameter
	shared_voter_state: SharedVoterState<AuthorityId>,
	shared_authority_set: SharedAuthoritySet<Hash, Block>,
}

impl<Hash, Block> GrandpaRpcHandler<Hash, Block> {
	pub fn new(
		shared_voter_state: SharedVoterState<AuthorityId>,
		shared_authority_set: SharedAuthoritySet<Hash, Block>
	) -> Self {
		Self {
			shared_voter_state,
			shared_authority_set,
		}
	}
}

#[derive(Serialize, Deserialize)]
pub struct RoundState {
	pub set_id: u64,
	pub round: u64,
	pub total_weight: u64,
	pub threshold_weight: u64,

	pub prevote_current_weight: u64,
	pub prevote_missing: HashSet<AuthorityId>,

	pub precommit_current_weight: u64,
	pub precommit_missing: HashSet<AuthorityId>,
}

impl RoundState {
	pub fn from<Hash, Block>(
		voter_state: &SharedVoterState<AuthorityId>,
		authority_set: &SharedAuthoritySet<Hash, Block>
	) -> Self
	where
		Hash: Debug + Clone + Eq + Send + Sync + 'static,
		Block: BlockNumberOps + Send + Sync + 'static,
	{
		let voter_state = voter_state.read().as_ref().map(|vs| vs.voter_state());
		// WIP: handle unwrap of lazily instantiated VoterState
		let voter_state = voter_state.unwrap();

		let current_authorities = authority_set.current_authorities();
		let voters: HashSet<AuthorityId> = current_authorities.voters().iter().map(|p| p.0.clone()).collect();

		let prevotes = voter_state.best_round.1.prevote_ids;
		let missing_prevotes = voters.difference(&prevotes).cloned().collect();

		let precommits = voter_state.best_round.1.precommit_ids;
		let missing_precommits = voters.difference(&precommits).cloned().collect();

		Self {
			set_id: authority_set.set_id(),
			round: voter_state.best_round.0,
			total_weight: voter_state.best_round.1.total_weight,
			threshold_weight: voter_state.best_round.1.threshold_weight,

			prevote_current_weight: voter_state.best_round.1.prevote_current_weight,
			prevote_missing: missing_prevotes,

			precommit_current_weight: voter_state.best_round.1.precommit_current_weight,
			precommit_missing: missing_precommits,
		}
	}
}

impl<Hash, Block: Send + Sync> GrandpaApi for GrandpaRpcHandler<Hash, Block> where
	Hash: Debug + Clone + Eq + Send + Sync + 'static,
	Block: BlockNumberOps + Send + Sync + 'static,
{
	fn grandpa_round_state(&self) -> FutureResult<RoundState> {
		let round_state = RoundState::from(&self.shared_voter_state, &self.shared_authority_set);
		let future = async move {
			Ok(round_state)
		}.boxed();
		Box::new(future.compat())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_test_runtime_client::{
		DefaultTestClientBuilderExt,
		TestClientBuilder,
		TestClientBuilderExt,
	};
	use std::sync::Arc;
	use jsonrpc_core::IoHandler;

	#[test]
	fn round_state() {
		let builder = TestClientBuilder::new();
		let client = builder.build();
		let client = Arc::new(client);

		let handler = GrandpaRpcHandler {};
		let mut io = IoHandler::new();
		io.extend_with(GrandpaApi::to_delegate(handler));

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","result":"Hello world","id":1}"#;

		assert_eq!(Some(response.into()), io.handle_request_sync(request));
	}
}
