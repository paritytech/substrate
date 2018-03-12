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

//! Dispatch system. Just dispatches calls.

use demo_primitives::{Function, Proposal, AccountId};
use runtime::{staking, system, session, democracy, council, council_vote, timestamp};

/// Dispatch a proposal.
pub fn proposal(proposal: Proposal) {
	match proposal {
		Proposal::SystemSetCode(ref a) =>
			system::privileged::set_code(a),
		Proposal::SessionSetLength(a) =>
			session::privileged::set_length(a),
		Proposal::SessionForceNewSession =>
			session::privileged::force_new_session(),
		Proposal::StakingSetSessionsPerEra(a) =>
			staking::privileged::set_sessions_per_era(a),
		Proposal::StakingSetBondingDuration(a) =>
			staking::privileged::set_bonding_duration(a),
		Proposal::StakingSetValidatorCount(a) =>
			staking::privileged::set_validator_count(a),
		Proposal::StakingForceNewEra =>
			staking::privileged::force_new_era(),
		Proposal::DemocracyCancelReferendum(a) =>
			democracy::privileged::cancel_referendum(a),
		Proposal::DemocracyStartReferendum(a, b) =>
			democracy::privileged::start_referendum(*a, b),
		Proposal::DemocracyCancelReferendum(a) =>
			democracy::privileged::cancel_referendum(a),
		Proposal::CouncilSetDesiredSeats(a) =>
			council::privileged::set_desired_seats(a),
		Proposal::CouncilRemoveMember(a) =>
			council::privileged::remove_member(&a),
		Proposal::CouncilSetPresentationDuration(a) =>
			council::privileged::set_presentation_duration(a),
		Proposal::CouncilSetTermDuration(a) =>
			council::privileged::set_term_duration(a),
		Proposal::CouncilVoteSetCooloffPeriod(a) =>
			council_vote::privileged::set_cooloff_period(a),
		Proposal::CouncilVoteSetVotingPeriod(a) =>
			council_vote::privileged::set_voting_period(a),
	}
}

/// Dispatch a function.
pub fn function(function: &Function, transactor: &AccountId) {
	match *function {
		Function::StakingStake =>
			staking::public::stake(transactor),
		Function::StakingUnstake =>
			staking::public::unstake(transactor),
		Function::StakingTransfer(dest, value) =>
			staking::public::transfer(transactor, &dest, value),
		Function::SessionSetKey(session) =>
			session::public::set_key(transactor, &session),
		Function::TimestampSet(t) =>
			timestamp::public::set(t),
		Function::CouncilVotePropose(ref a) =>
			council_vote::public::propose(transactor, a),
		Function::CouncilVoteVote(ref a, b) =>
			council_vote::public::vote(transactor, a, b),
		Function::CouncilVoteVeto(ref a) =>
			council_vote::public::veto(transactor, a),
		Function::CouncilSetApprovals(ref a, b) =>
			council::public::set_approvals(transactor, a, b),
		Function::CouncilReapInactiveVoter(a, ref b, c, d) =>
			council::public::reap_inactive_voter(transactor, a, b, c, d),
		Function::CouncilRetractVoter(a) =>
			council::public::retract_voter(transactor, a),
		Function::CouncilSubmitCandidacy(a) =>
			council::public::submit_candidacy(transactor, a),
		Function::CouncilPresentWinner(ref a, b, c) =>
			council::public::present_winner(transactor, a, b, c),
		Function::DemocracyPropose(ref a, b) =>
			democracy::public::propose(transactor, a, b),
		Function::DemocracySecond(a) =>
			democracy::public::second(transactor, a),
		Function::DemocracyVote(a, b) =>
			democracy::public::vote(transactor, a, b),
	}
}
