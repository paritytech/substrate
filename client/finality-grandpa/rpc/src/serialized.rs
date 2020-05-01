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

use serde::{Deserialize, Serialize};
use std::{fmt::Debug, collections::HashSet};
use finality_grandpa::BlockNumberOps;

use sc_finality_grandpa::{AuthorityId, SharedAuthoritySet, SharedVoterState, report};
use crate::error::Error;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Prevotes {
	current_weight: u32,
	missing: HashSet<AuthorityId>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Precommits {
	current_weight: u32,
	missing: HashSet<AuthorityId>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RoundState {
	round: u32,
	total_weight: u32,
	threshold_weight: u32,
	prevotes: Prevotes,
	precommits: Precommits,
}

impl RoundState {
	fn from(
		round: u64,
		round_state: &report::RoundState<AuthorityId>,
		voters: &HashSet<AuthorityId>,
	) -> Result<Self, Error> {
		use std::convert::TryInto;

		let prevotes = &round_state.prevote_ids;
		let missing_prevotes = voters.difference(&prevotes).cloned().collect();

		let precommits = &round_state.precommit_ids;
		let missing_precommits = voters.difference(&precommits).cloned().collect();

		Ok(Self {
			round: round.try_into()?,
			total_weight: round_state.total_weight.get().try_into()?,
			threshold_weight: round_state.threshold_weight.get().try_into()?,
			prevotes: Prevotes {
				current_weight: round_state.prevote_current_weight.0.try_into()?,
				missing: missing_prevotes,
			},
			precommits: Precommits {
				current_weight: round_state.precommit_current_weight.0.try_into()?,
				missing: missing_precommits,
			},
		})
	}
}

/// The state of the current best round, as well as the background rounds in a
/// form suitable for serialization.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportedRoundStates {
	set_id: u32,
	best: RoundState,
	background: Vec<RoundState>,
}

impl ReportedRoundStates {
	pub fn from<Hash, Block>(
		voter_state: &SharedVoterState,
		authority_set: &SharedAuthoritySet<Hash, Block>,
	) -> Result<Self, Error>
	where
		Hash: Debug + Clone + Eq + Send + Sync + 'static,
		Block: BlockNumberOps + Send + Sync + 'static,
	{
		use std::convert::TryFrom;

		let voter_state = voter_state
			.voter_state()
			.ok_or(Error::EndpointNotReady)?;

		let current_voters: HashSet<AuthorityId> = authority_set
			.current_authorities()
			.iter()
			.map(|p| p.0.clone())
			.collect();

		let set_id = u32::try_from(authority_set.set_id())
			.map_err(|_| Error::AuthoritySetIdReportedAsUnreasonablyLarge)?;

		let best = {
			let (round, round_state) = voter_state.best_round;
			RoundState::from(round, &round_state, &current_voters)?
		};

		let background = voter_state
			.background_rounds
			.iter()
			.map(|(round, round_state)| RoundState::from(*round, round_state, &current_voters))
			.collect::<Result<Vec<_>, Error>>()?;

		Ok(Self {
			set_id,
			best,
			background,
		})
	}
}
