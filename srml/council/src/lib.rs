// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! # Council Module
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! ## Overview
//!
//! The Council system module provides functionality for different voting systems to handle the voting in and maintenance of council members, including:
//!
//! * Council Motions
//! * Council Seats
//! * Council Voting
//!
//! - [`council::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ### Terminology
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! #### Council Proposals
//!
//! * **Councillor** A councillor is a countable stakeholder. They may vote on a council proposal during the voting period if they did not create the proposal.
//! * **Council motion:** A mechanism used enact an outer `Call` dispatch (of type `Proposal`) from a council origin.
//! * **Council motion vote:** Allows an arbitrary number of councillors (other than the councillor that proposed the motion) to vote and initiate a call. 
//! * **Council origin:** The council origin is the council (not root) and contains the council motion mechanism. It has different mechanics to other origins.
//! * **Council proposal validity prerequisites:** A council proposal is valid when it is submitted by a councillor, is not a duplicate proposal, has not been vetoed, and when the council term does not expire before the proposals' voting period has lapsed.
//! * **Council proposal creation storage** A council proposal after being deemed valid is stored as follows:
//!   * Proposals' storage vector is updated with a tuple containing the proposal's hash and the expiry block number of its voting period.
//!   * Proposals' hash is mapped to the proposals' value in storage using `ProposalOf`.
//!   * Proposals' hash is mapped to a vector of account ids that have voted the proposal in storage using `ProposalVoters`. Initially the account id of the councillor that created the proposal is added to the vector.
//!   * Councillor's vote storage tuple `CouncilVoteOf` is updated with a mapping between the proposal's hash and the councillor's account id. Initially the councillor that created the proposal is added with a vote of yay.
//! * **Council proposal postponement** Councillors that abstain from voting may postpone a council proposal from being approved or disapproved. Note: Postponing is equivalent to a **council proposal veto** since the veto only lasts for the cooldown period.
//!
//! #### Council Proposal Voting
//!
//! * **Council proposal vote storage** A council proposal vote that occurs after council proposal creation is stored as follows:
//!   * `ProposalVoters` storage vector (containing account ids that have voted for the proposal's hash) is updated with the councillor's new vote.
//!   * Councillor's vote storage tuple `CouncilVoteOf` is updated with a mapping between a tuple containing the proposal's hash, the councillor's account id, and their new vote.
//!	  * `Voting` storage mapping is updated with the councillor's vote.
//! 	* Note that `Voting` maps the proposal's hash to a tuple containing the corresponding proposal's index, vote threshold, and vectors containing both yay and nay voter account ids. 
//! * **Council proposal voting rules** Duplicate votes from the same councillor are ignored. Councillors may swap their vote from yay to nay and vice versa.
//! * **Council proposal vote threshold** A council proposal that is created with a threshold level of one is voted upon and approved by the councillor that created it, and then executed. Whereas a council proposal with a threshold level of more than one is added to the `Voting` storage mapping.
//! * **Council proposal voting veto rules** A councillor may veto a proposal if it's stored in the `ProposalVoters` mapping, on condition that they have not vetoed it previously. Once a councillor vetoes a council proposal they cannot propose the proposal again until after a cooling off period that's measured in blocks.
//! * **Council proposal voting veto** If a councillors veto is valid then their veto is stored in `VetoedProposal` amongst other councillors that have vetoed the proposal. `VetoedProposal` maps the proposal's hash to a tuple comprising of the block number when the veto expires, and the account id of the vetoer. Vetoed proposals are removed from various storage locations, including the `Proposals` storage vector, the `ProposalsOf` storage mapping, the `ProposalVoters` storage mapping, and the `CouncilVoteOf` mapping. A veto cancels a proposal, but the veto is not considered a vote.
//! * **Council proposal voting cancellation** The `on_finalise` signature is used in the module declaration to run anything that needs to be done at the end of the block. In council proposal voting it calls a private function `end_block` with the current block as an argument, which loops through each proposal in storage whose voting period ends at the given block. For each proposal it calls `is_aux_sub_type` and destructures the return value. The return value is a call to a function `cancel_referendum` with a `ref_index` (referendum index) argument that removes the referendum with that referendum index. When the call to the return value `cancel_referendum` returns a value, then we know that this council proposal was elevated to the table of referenda and therefore has a referendum index. We also already know that it expires on this block, so we may proceed to cancels the referendum by: dispatching event `TallyCancelation` to indicate that a voting tally has happened associated with a cancellation vote for the referendum associated with the given proposal; and by the council directly calling `internal_cancel_referendum` to remove the specific referendum with the given referendum index, but doing so is only permitted if the voting tally for the proposal was a unanimous vote (i.e. no nays, no abstainers).
//! * **Council proposal voting elevation** The `on_finalise` signature is used in the module declaration to run anything that needs to be done at the end of the block. In council proposal voting it calls a private function `end_block` with the current block as an argument, which loops through each proposal in storage whose voting period ends at the given block. For each proposal it calls `is_aux_sub_type` and destructures the return value. When the call to `is_aux_sub_type` with the current proposal does not destructure to a function call that is able to cancel a referendum index associated with the proposal, then we know this council proposal has not yet been elevated to the table of referenda, so we may proceed to check the vote tally to determine whether to start the referendum. If it starts the referendum it dispatches an event `TallyReferendum` to indicate that a voting tally has started for the referendum. If the voting tally has more yay votes than the combination of all nay votes and abstainers, then it removes any veto imposed upon the council proposal (since the proposal voting period is expiring). If the council voting tally was unanimous then it starts a referendum (elevating the proposal to the table of referendum) with a vote threshold of `SuperMajorityAgainst`. Otherwise if there were any nay voters or abstainers at the end of the council voting period then it starts a referendum (elevating the proposal to the table of referendum) with a vote threshold of `SimplyMajority`.
//! * **Council proposal voting approval/disapproval** When the **council proposal voting tally** of yay votes reach its threshold level during its voting period then it's approved and elevated to the table of active referendum on the next block. Once the tally of votes results in the council proposal being approved or disapproved, we remove the motion from the `Voting` storage mapping, and remove the proposal hash from the list of active proposals `Proposals`.
//! * **Council proposal voting approval (simply majority / majority agreement)** If the tally of yay votes for a council proposal reaches its threshold level during its voting period and a majority council agreement occurs whereby its tally from majority voting results in a simple majority (i.e. more explicit yay than nay votes, which signals a sensible and uncontroversial proposal), then it is approved. When executed it is elevated to the table of active referenda on the next block, and a vote threshold of simple majority is applied to the referendum.
//! * **Council proposal voting approval (unanimous / super majority against)** If a unanimous voting tally for the council proposal occurs and results in a unanimous council agreement (i.e. only yay votes), then it is approved. When executed it is elevated to the table of active referenda on the next block, and a vote threshold of 'super majority against' is applied to the referendum. It uses a negative [AQB](https://docs.substrate.dev/docs/glossary#section-adaptive-quorum-biasing-aqb-) to encourage councillors not to abstain. A single veto from a councillor cancels the proposal and prevents the agreement. Council proposals submitted this way must have over 50% approval since abstention votes will be biased in favour of the proposal (alongside any nay votes).
//! * **Referenda** Each council or public proposal that is elevated to the table of referenda is instantly executed autonomously once its vote count reaches its threshold level for approval.
//!
//! #### Council Seats
//!
//! * **Candidate approval voting call** Express candidate approval voting is a public call that anyone may execute by signing and submitting an extrinsic. We ensure that information about the `origin` where the dispatch initiated is a signed account using `ensure_signed`. It performs an `O(1)` operation that involves one extra database entry and one database change.
//! * **Candidate registration and vote index** Candidate approval votes are only considered before the presentation period and for candidates that have a registered list slot with an approved candidate index `VoteIndex`.
//! * **Candidate voters security bond (for the first vote)** If it's the voter's first vote and its valid, then before enacting any operation and changing the storage, a security bond is deducted from them using the `reserve` function of the Balances module, as it may result in a major alteration of storage. The bond amount should be sufficient to cover any costs of the substantial execution in case the operation cannot proceed. The bond is a mitigation measure against the classical blockchain attack scenario since we cannot be certain that the operation will not require substantial computation. The voters account id is pushed onto the `Voters` vector that contains the list of present voters.
//! * **Candidate voters' subsequent votes (after their first vote)** If the voter makes a subsequent vote that's valid, then: their vote is recorded in `LastActiveOf`, which maps their account id to the last cleared vote index that they were active at; and the votes (i.e. yay or nay) for each candidate with a vote index is added to the `ApprovalsOf` mapping.
//! * **Candidate voter inactivity reaping prerequisites** Reaping inactive voters is only considered valid after satisfying the following prerequisites: It must occur before the presentation period; both the reporter and the target must have already voted and have been recorded in `LastActiveOf`; the assumed vote index occurs after an inactivity grace period (vote indexes remaining after the target voter's last active vote and when their associated approval votes are uncertain); both the given reporters' vote index and the given targets' vote index exist; the candidates' approved index `VoteIndex` exists and matches the vote index that the reporter assumed was correct.
//! * **Candidate voter inactivity reaping claim validity determination** Upon satisfying the **candidate voter inactivity reaping prerequisites**, we determine whether the reporter has made a valid claim that the target account was in fact inactive. If the claim is true then we remove the targets' inactive account, otherwise we remove the account that falsely reported their inactivity. To determine the validity of the claim, we enumerate over two lists in parallel: `approvals_of` (maps the account id of the target voter to their list of votes for the last vote index when their vote was active); and `candidates` (the current list of candidate account ids). Then if none of the following are true, we deem the reporters' claim invalid: If any of the candidate account ids has a list of votes to the last vote index; and if any of the candidate account ids isn't the default; and if using `RegisterInfoOf` and any of the candidate account ids maps to a corresponding vote index when they registered that is less than or equal to the target voters last active vote index. This would indicate that the candidate registered before the last vote index `LastActiveOf` when the target voter was last active, and means it is in fact a valid claim to state that the target voter was an inactive voter between their registration and the last activate vote.
//! * **Candidate voter inactivity reaping** Removing an inactive voter is a public call. It performs an `O(1)` operation that involves one fewer database entry and one database change. After determining the result of the claim validity, we call `remove_voter` as follows, depending on the claim validity: If the claim was valid we delete the inactive voter using the associated vote index and their list of approval votes; or if the claim was invalid we delete the reporter (due to the target account actually still being active). Lastly we perform the reaping as follows, depending the claim validity: If the claim was valid then we call `repatriate_reserved` to slash the target account of their voter bond and move that value from their reserved account balance to the free balance of the reporter (beneficiary), then emit a `VoterReaped` event; if the claim was invalid then we call `slash_reserved` to slash the reporter for their bad behaviour in making a false claim. The reporter's account is slashed by deducting a value from their reserved balance, and by decreasing the total amount of stake in the system by the amount that was slashed, then we emit a `BadReaperSlashed` event.
//!
//! ### Goals
//!
//! The Council module in Substrate is designed to make the following possible:
//!
//! * Creation of council proposals using the council motion mechanism by councillors.
//! * Validation of council proposals.
//! * Tallying votes of council proposals by councillors during the proposals' voting period.
//! * Vetoing (postponement) of council proposals through abstainment by councillors for a cooldown period.
//! * Elevation of council proposals to start an associated referenda on the table of referenda.
//! * Applying vote thresholds to referenda depending on their associated council proposal voting approval tally.
//! * Instant autonomous execution of referenda once their vote tally reaches the vote threshold level of approval.
//! * Cancellation of council proposals that were elevated as associated referenda onto the table of referenda.
//! * Candidate registration in list slots (necessary to receive candidate approval votes during the presentation period).
//! * Deduction of security bonds from candidate voters.
//! * Express council seat candidate approval voting.
//! * Reaping of candidate voters due to valid claims of their inactivity by reporters.
//! * Reaping reporters that lodge invalid claims of candidate voter inactivity.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### Council Motions
//!
//! * `propose` - Create a council proposal using the council motion mechanism by a councillor who provides a vote threshold.
//! * `vote` - Update the approval vote tally through active councillors voting on a council proposal. Approve and execute it when the vote tally reaches the vote threshold. Disapprove it when the potential votes remaining is less than the threshold.
//!
//! #### Council Seats
//!
//! * `set_approvals` - Set candidate approvals. Approval slots stay valid as long as candidates in those slots are registered.
//! * `proxy_set_approvals` - Set candidate approvals from a proxy. Approval slots stay valid as long as candidates in those slots are registered.
//! * `reap_inactive_voter` - Remove a voter. Can be called by anyone. Returns the voter deposit to the `signed` origin.
//! * `retract_voter` - Remove a voter. All votes are cancelled and the voter deposit is returned.
//! * `submit_candidacy` - Submit oneself for candidacy. Account must have enough transferrable funds in it to pay the bond.
//! * `present_winner` - Claim that the `signed` origin is one of the top candidates.
//! * `set_desired_seats` - Set the desired council member count.
//! * `remove_member` - Remove a council member immediately. A tally happens instantly (if not already in a presentation period) to fill the seat if removal means that the desired members are not met.
//! * `set_presentation_duration` - Set the presentation duration.
//! * `set_term_duration` - Set the term duration.
//! * `on_finalize` - Signature declaration that runs anything that needs to be done at the end of the block.
//!
//! #### Council Voting
//!
//! * `propose` - Propose a council proposal.
//! * `vote` - Vote on a council proposal by a councillor.
//! * `veto` - Veto a council proposal by a councillor.
//! * `set_cooloff_period` - Specify cooling off period.
//! * `set_voting_period` - Specify voting period.
//! * `on_finalize` - Signature declaration that runs anything that needs to be done at the end of the block.
//!
//! ### Public Functions
//!
//! #### Council Motions
//!
//! * `is_councillor` - Check if a councillor is a member of the active council.
//!
//! #### Council Seats
//!
//! * `presentation_active` - Check if we're currently in a presentation period.
//! * `is_a_candidate` - Check if a specific account id is a registered candidate.
//! * `next_vote_from` - Determine the block when a vote can occur.
//! * `next_tally` - The block number when the tally for the next election will occur.
//!
//! #### Council Voting
//!
//! * `is_vetoed` - Check if a council proposal has been vetoed.
//! * `will_still_be_councillor_at` - Check each account id of the active council to determine what block number they will still be active.
//! * `is_councillor` - Check if a given account id is a councillor.
//! * `tally` - Tally's council votes.
//!
//! ## Usage
//!
//! ### Prerequisites
//!
//! Import the Council module and types and derive your runtime's configuration traits from the Council module trait.
//!
//! ### Simple Code Snippet
//!
//! See the tests contained in files in this module's directory for simple code snippets that may make this module's functionalities clearer.
//!
//! ## Related Modules
//!
//! * [`System`](../srml_system/index.html)
//! * [`Support`](../srml_support/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

pub mod voting;
pub mod motions;
pub mod seats;

pub use crate::seats::{Trait, Module, RawEvent, Event, VoteIndex};

#[cfg(test)]
mod tests {
	// These re-exports are here for a reason, edit with care
	pub use super::*;
	pub use runtime_io::with_externalities;
	use srml_support::{impl_outer_origin, impl_outer_event, impl_outer_dispatch};
	pub use substrate_primitives::H256;
	pub use primitives::BuildStorage;
	pub use primitives::traits::{BlakeTwo256, IdentityLookup};
	pub use primitives::testing::{Digest, DigestItem, Header};
	pub use substrate_primitives::{Blake2Hasher};
	pub use {seats, motions, voting};

	impl_outer_origin! {
		pub enum Origin for Test {
			motions
		}
	}

	impl_outer_event! {
		pub enum Event for Test {
			balances<T>, democracy<T>, seats<T>, voting<T>, motions<T>,
		}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			balances::Balances,
			democracy::Democracy,
		}
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type Log = DigestItem;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = Event;
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
	}
	impl democracy::Trait for Test {
		type Currency = balances::Module<Self>;
		type Proposal = Call;
		type Event = Event;
	}
	impl seats::Trait for Test {
		type Event = Event;
		type BadPresentation = ();
		type BadReaper = ();
	}
	impl motions::Trait for Test {
		type Origin = Origin;
		type Proposal = Call;
		type Event = Event;
	}
	impl voting::Trait for Test {
		type Event = Event;
	}

	pub fn new_test_ext(with_council: bool) -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(balances::GenesisConfig::<Test>{
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
			existential_deposit: 0,
			transfer_fee: 0,
			creation_fee: 0,
			vesting: vec![],
		}.build_storage().unwrap().0);
		t.extend(democracy::GenesisConfig::<Test>{
			launch_period: 1,
			voting_period: 3,
			minimum_deposit: 1,
			public_delay: 0,
			max_lock_periods: 6,
		}.build_storage().unwrap().0);
		t.extend(seats::GenesisConfig::<Test> {
			candidacy_bond: 9,
			voter_bond: 3,
			present_slash_per_voter: 1,
			carry_count: 2,
			inactive_grace_period: 1,
			active_council: if with_council { vec![
				(1, 10),
				(2, 10),
				(3, 10)
			] } else { vec![] },
			approval_voting_period: 4,
			presentation_duration: 2,
			desired_seats: 2,
			term_duration: 5,
		}.build_storage().unwrap().0);
		t.extend(voting::GenesisConfig::<Test> {
			cooloff_period: 2,
			voting_period: 1,
			enact_delay_period: 0,
		}.build_storage().unwrap().0);
		runtime_io::TestExternalities::new(t)
	}

	pub type System = system::Module<Test>;
	pub type Balances = balances::Module<Test>;
	pub type Democracy = democracy::Module<Test>;
	pub type Council = seats::Module<Test>;
	pub type CouncilVoting = voting::Module<Test>;
	pub type CouncilMotions = motions::Module<Test>;
}
