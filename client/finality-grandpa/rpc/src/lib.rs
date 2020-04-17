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

use finality_grandpa::BlockNumberOps;
use sc_finality_grandpa::{voter, AuthorityId, SharedAuthoritySet, SharedVoterState};

use futures::{FutureExt, TryFutureExt};
use jsonrpc_derive::rpc;
use log::warn;
use serde::{Deserialize, Serialize};
use std::{collections::HashSet, fmt::Debug};

type FutureResult<T> =
    Box<dyn jsonrpc_core::futures::Future<Item = T, Error = jsonrpc_core::Error> + Send>;

#[derive(derive_more::Display, derive_more::From)]
pub enum Error {
    #[display(fmt = "GRANDPA RPC endpoint not ready")]
    EndpointNotReady,
}

impl From<Error> for jsonrpc_core::Error {
    fn from(error: Error) -> Self {
        jsonrpc_core::Error {
            message: format!("{}", error).into(),
            // WIP: what error code should we use?
            code: jsonrpc_core::ErrorCode::ServerError(1234),
            data: None,
        }
    }
}

#[rpc]
pub trait GrandpaApi {
    #[rpc(name = "grandpa_roundState")]
    fn round_state(&self) -> FutureResult<ReportedRoundStates>;
}

pub struct GrandpaRpcHandler<Hash, Block> {
    shared_voter_state: SharedVoterState<AuthorityId>,
    shared_authority_set: SharedAuthoritySet<Hash, Block>,
}

impl<Hash, Block> GrandpaRpcHandler<Hash, Block> {
    pub fn new(
        shared_voter_state: SharedVoterState<AuthorityId>,
        shared_authority_set: SharedAuthoritySet<Hash, Block>,
    ) -> Self {
        Self {
            shared_voter_state,
            shared_authority_set,
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Prevotes {
    pub current_weight: u64,
    pub missing: HashSet<AuthorityId>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Precommits {
    pub current_weight: u64,
    pub missing: HashSet<AuthorityId>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RoundState {
    pub round: u64,
    pub total_weight: u64,
    pub threshold_weight: u64,
    pub prevotes: Prevotes,
    pub precommits: Precommits,
}

impl RoundState {
    pub fn from(
        round: u64,
        round_state: &voter::report::RoundState<AuthorityId>,
        voters: &HashSet<AuthorityId>,
    ) -> Self {
        let prevotes = &round_state.prevote_ids;
        let missing_prevotes = voters.difference(&prevotes).cloned().collect();

        let precommits = &round_state.precommit_ids;
        let missing_precommits = voters.difference(&precommits).cloned().collect();

        Self {
            round,
            total_weight: round_state.total_weight,
            threshold_weight: round_state.threshold_weight,
            prevotes: Prevotes {
                current_weight: round_state.prevote_current_weight,
                missing: missing_prevotes,
            },
            precommits: Precommits {
                current_weight: round_state.precommit_current_weight,
                missing: missing_precommits,
            },
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportedRoundStates {
    pub set_id: u64,
    pub best: RoundState,
    pub background: Vec<RoundState>,
}

impl ReportedRoundStates {
    pub fn from<Hash, Block>(
        voter_state: &SharedVoterState<AuthorityId>,
        authority_set: &SharedAuthoritySet<Hash, Block>,
    ) -> Result<Self, Error>
    where
        Hash: Debug + Clone + Eq + Send + Sync + 'static,
        Block: BlockNumberOps + Send + Sync + 'static,
    {
        let voter_state = voter_state
            .read()
            .as_ref()
            .map(|vs| vs.voter_state())
            .ok_or(Error::EndpointNotReady)?;

        let current_voters: HashSet<AuthorityId> = authority_set
            .current_authorities()
			.voters()
            .iter()
            .map(|p| p.0.clone())
            .collect();

        let set_id = voter_state.best_round.0;
        if voter_state.best_round.0 != authority_set.set_id() {
            warn!("Set ID from AuthoritySet does not match VoterState?")
        }

        let best = {
            let (round, round_state) = voter_state.best_round;
            RoundState::from(round, &round_state, &current_voters)
        };

        let background = voter_state
            .background_rounds
            .iter()
            .map(|(round, round_state)| RoundState::from(*round, round_state, &current_voters))
            .collect();

        Ok(Self {
            set_id,
            best,
            background,
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use jsonrpc_core::IoHandler;
    use std::sync::Arc;
    use substrate_test_runtime_client::{
        DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
    };

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
