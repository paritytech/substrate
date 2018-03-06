// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Democratic system: Handles administration of general stakeholder voting.

use demo_primitives::Proposal;
use runtime::{staking, system, session, democracy};

pub fn enact_proposal(proposal: Proposal) {
	match proposal {
		Proposal::SystemSetCode(code) => {
			system::privileged::set_code(&code);
		}
		Proposal::SessionSetLength(value) => {
			session::privileged::set_length(value);
		}
		Proposal::SessionForceNewSession => {
			session::privileged::force_new_session();
		}
		Proposal::StakingSetSessionsPerEra(value) => {
			staking::privileged::set_sessions_per_era(value);
		}
		Proposal::StakingSetBondingDuration(value) => {
			staking::privileged::set_bonding_duration(value);
		}
		Proposal::StakingSetValidatorCount(value) => {
			staking::privileged::set_validator_count(value);
		}
		Proposal::StakingForceNewEra => {
			staking::privileged::force_new_era()
		}
		Proposal::DemocracyCancelReferendum(ref_index) => {
			democracy::privileged::cancel_referendum(ref_index)
		}
	}
}
