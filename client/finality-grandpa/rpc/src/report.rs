// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::{
	collections::{BTreeSet, HashSet},
	fmt::Debug,
	ops::Add,
};

use serde::{Deserialize, Serialize};

use sc_finality_grandpa::{report, AuthorityId, SharedAuthoritySet, SharedVoterState};

use crate::error::Error;

/// Utility trait to get reporting data for the current GRANDPA authority set.
pub trait ReportAuthoritySet {
	fn get(&self) -> (u64, HashSet<AuthorityId>);
}

/// Utility trait to get reporting data for the current GRANDPA voter state.
pub trait ReportVoterState {
	fn get(&self) -> Option<report::VoterState<AuthorityId>>;
}

impl<H, N> ReportAuthoritySet for SharedAuthoritySet<H, N>
where
	N: Add<Output = N> + Ord + Clone + Debug,
	H: Clone + Debug + Eq,
{
	fn get(&self) -> (u64, HashSet<AuthorityId>) {
		let current_voters: HashSet<AuthorityId> =
			self.current_authorities().iter().map(|p| p.0.clone()).collect();

		(self.set_id(), current_voters)
	}
}

impl ReportVoterState for SharedVoterState {
	fn get(&self) -> Option<report::VoterState<AuthorityId>> {
		self.voter_state()
	}
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Prevotes {
	current_weight: u32,
	missing: BTreeSet<AuthorityId>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Precommits {
	current_weight: u32,
	missing: BTreeSet<AuthorityId>,
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
		let prevotes = &round_state.prevote_ids;
		let missing_prevotes = voters.difference(prevotes).cloned().collect();

		let precommits = &round_state.precommit_ids;
		let missing_precommits = voters.difference(precommits).cloned().collect();

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
	pub fn from<AuthoritySet, VoterState>(
		authority_set: &AuthoritySet,
		voter_state: &VoterState,
	) -> Result<Self, Error>
	where
		AuthoritySet: ReportAuthoritySet,
		VoterState: ReportVoterState,
	{
		let voter_state = voter_state.get().ok_or(Error::EndpointNotReady)?;

		let (set_id, current_voters) = authority_set.get();
		let set_id =
			u32::try_from(set_id).map_err(|_| Error::AuthoritySetIdReportedAsUnreasonablyLarge)?;

		let best = {
			let (round, round_state) = voter_state.best_round;
			RoundState::from(round, &round_state, &current_voters)?
		};

		let background = voter_state
			.background_rounds
			.iter()
			.map(|(round, round_state)| RoundState::from(*round, round_state, &current_voters))
			.collect::<Result<Vec<_>, Error>>()?;

		Ok(Self { set_id, best, background })
	}
}
