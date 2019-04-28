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
//! The Council module provides functionality for different voting systems to handle the voting in and maintenance of council members.
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
//! - **Councils' role** The councils' role is to: propose sensible referenda, cancel potentially dangerous or
//!
//! malicious referenda, and to represent passive stakeholders.
//!
//! - **Council member** (councillor) - A countable stakeholder represented by an on-chain
//! account. They may vote on council proposals from other councillors during the voting period.
//!
//! - **Council motion** A mechanism used to enact a proposal from a council origin.
//!
//! - **Council origin** The council (not root) that contains the council motion mechanism.
//!
//! - **Council proposal** A submission by a councillor. An initial vote of yay from that councillor is applied
//! to `CouncilVoteOf`.
//!
//! - **Council proposals' validity** A council proposal is valid when it's unique, hasn't yet been vetoed, and
//! when the council term doesn't expire before block number when the proposals' voting period ends.
//!
//! - **Council proposal postponement** Councillors that abstain from voting may postpone a council proposal from
//! being approved or disapproved. Postponement is equivalent to a veto, which only lasts for the cooldown period.
//!
//! #### Council Proposal Voting
//!
//! - **Council proposal vote** A vote of yay or nay from a councillor on a single proposal that is stored in the
//! `ProposalVoters`, `CouncilVoteOf`, and `Voting` mappings. Councillors may change their vote.
//!
//! - **Council proposal veto** A council member may veto any council proposal that exists and is stored in
//! `ProposalVoters` only once. A vetoed proposal that's valid is stored in `VetoedProposal` for a cooling off period
//! that's measured in blocks. The vetoer cannot propose the proposal again until the veto expires.
//!
//! - **Council proposal vote cancellation** At the end of a given block we cancel all referenda that have been
//! elevated to the table of referenda whose voting period ends at that block and where the outcome of their voting
//! tally result was a unanimous (i.e. no nays, no abstainers) vote to cancel the referendum.
//!
//! - **Council voting process to elevate a proposal to the table of referenda** At the end of a given block we
//! establish a list of referenda that haven't already been elevated to the table of referenda (i.e. those that aren't
//! cancellable) and whose voting period ends at that block, then we check the voting tally for each referendum in the
//! resulting list to determine what action to take. If the outcome of its voting tally council was unanimous then
//! it starts a referendum (elevating the proposal to the table of referenda) with a vote threshold of
//! `SuperMajorityAgainst`. Otherwise if it wasn't unanimous (if there were any nay voters or abstainers) then it
//! still starts a referendum (elevating the proposal to the table of referendum) but instead applies a vote threshold
//! of `SimplyMajority`. Lastly, if the voting tally has more yay votes than the combination of all nay votes
//! and abstainers, then it removes any veto imposed upon the council proposal (since the proposal voting period
//! is expiring).
//!
//! - **Council proposal voting approval (simply majority / majority agreement)** Upon the voting tally of yay
//! votes for a council proposal reaching its threshold level for approval during its voting period, and where a
//! majority council agreement occurs, whereby its tally from majority voting results in a simple majority
//! (i.e. more explicit yay than nay votes, which signals a sensible and uncontroversial proposal), then the council
//! proposal is approved. When executed, it is elevated to the table of active referenda on the next block,
//! and a vote threshold of 'simple majority' is applied to the referendum.
//!
//! - **Council proposal voting approval (unanimous / super majority against)** If a unanimous voting tally for the
//! council proposal occurs and results in a unanimous council agreement (i.e. only yay votes), then it is approved.
//! When executed it is elevated to the table of active referenda on the next block, and a vote threshold of
//! 'super majority against' is applied to the referendum. A negative
//! [AQB](https://docs.substrate.dev/docs/glossary#section-adaptive-quorum-biasing-aqb-) is used to discourage
//! councillors from abstaining. A single veto from a councillor cancels the proposal and prevents the agreement.
//! Council proposals submitted this way must have over 50% approval since abstention votes will be biased in favour
//! of the proposal (alongside any nay votes).
//!
//! - **Referenda** Each council or public proposal that is elevated as referenda to the table of referenda is
//! instantly executed autonomously once its vote count reaches its threshold level for approval.
//!
//! #### Council Seats
//!
//! - **Candidate approval voting call** Express candidate approval voting is a public call that anyone may execute
//! by signing and submitting an extrinsic. We ensure that information about the `origin` where the dispatch initiated
//! is a signed account using `ensure_signed`.
//!
//! - **Candidate registration and vote index** Candidate approval votes are only considered before the presentation
//! period and for candidates that have a registered list slot with an approved candidate index `VoteIndex`.
//!
//!  - **Candidate voters security bond (for the first vote)** If it's the voter's first vote and their vote is valid,
//! then before enacting any operation and changing the storage, a security bond is deducted from them using the
//! `reserve` function of the Balances module, as it may result in a major alteration of storage. The bond amount
//! should be sufficient to cover any costs of the substantial execution in case the operation cannot proceed.
//! The bond is a mitigation measure against the classical blockchain attack scenario since we cannot be certain
//! that the operation will not require substantial computation. The voters' account id is added to the list `Voters`
//! of present voters.
//!
//! - **Candidate voters' subsequent votes (after their first vote)** If the voter makes a subsequent vote that's
//! valid, then their vote is recorded in `LastActiveOf`, which maps their account id to the last cleared vote index
//! that they were active at, and the votes (i.e. yay or nay) for each candidate with a vote index are added to the
//! `ApprovalsOf` mapping.
//!
//! - **Candidate voter inactivity reaping process** After determining the claims' validity, we call `remove_voter`
//! as follows depending on the claim validity: if the claim was valid delete the inactive voter, otherwise delete
//! the reporter. Lastly we perform reaping as follows, depending on the claim validity: if the claim is valid call
//! `repatriate_reserved` to slash the target account of their voter bond and move that value from the targets'
//! reserved account balance to the free balance of the reporter (beneficiary) and emit a `VoterReaped` event,
//! otherwise if the claim was invalid call `slash_reserved` to slash the reporter for their bad behaviour in making a
//! false claim. The reporter's account is slashed by deducting a value from their reserved balance, and by decreasing
//! the total amount of stake in the system by the amount that was slashed, then we emit a `BadReaperSlashed` event.
//!
//! ### Goals
//!
//! The Council module in Substrate is designed to make the following possible:
//!
//! - Creation of council proposals by councillors using the council motion mechanism.
//! - Validation of council proposals.
//! - Tallying votes of council proposals by councillors during the proposals' voting period.
//! - Vetoing (postponement) of council proposals for a cooldown period through abstention by councillors.
//! - Elevation of council proposals to start an associated referenda on the table of referenda.
//! - Applying vote thresholds to referenda depending on their associated council proposal voting approval tally.
//! - Instant autonomous execution of referenda once their vote tally reaches the vote threshold level of approval.
//! - Cancellation of council proposals that were elevated as associated referenda onto the table of referenda.
//! - Candidate registration in list slots (necessary to receive candidate approval votes during the
//!   presentation period).
//! - Deduction of security bonds from candidate voters.
//! - Express council seat candidate approval voting.
//! - Reaping of candidate voters due to valid claims of their inactivity by reporters.
//! - Reaping reporters that lodge invalid claims of candidate voter inactivity.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### Council Motions
//!
//! - `propose` - Create a council proposal using the council motion mechanism by a councillor who provides a vote
//! threshold.
//! - `vote` - Update the approval vote tally through active councillors voting on a council proposal. Approve and
//! execute it when the vote tally reaches the vote threshold. Disapprove it when the potential votes remaining is
//! less than the threshold.
//!
//! #### Council Seats
//!
//! - `set_approvals` - Set candidate approvals. Approval slots stay valid as long as candidates in those slots are
//! registered.
//! - `proxy_set_approvals` - Set candidate approvals from a proxy. Approval slots stay valid as long as candidates
//! in those slots are registered.
//! - `reap_inactive_voter` - Remove a voter. Can be called by anyone who is a voter. At the end of this call,
//! either the reported or the reportee will get removed.
//! - `retract_voter` - Remove a voter. All votes are cancelled and the voter deposit is returned.
//! - `submit_candidacy` - Submit oneself for candidacy. Account must have enough transferrable funds in it to pay
//! the bond.
//! - `present_winner` - Claim that the `signed` origin is one of the top candidates.
//! - `set_desired_seats` - Set the desired council member count.
//! - `remove_member` - Remove a council member immediately. A tally happens instantly (if not already in a
//! presentation period) to fill the seat if removal means that the desired members are not met.
//! - `set_presentation_duration` - Set the presentation duration.
//! - `set_term_duration` - Set the term duration.
//!
//! #### Council Voting
//!
//! - `propose` - Propose a council proposal.
//! - `vote` - Vote on a council proposal by a councillor.
//! - `veto` - Veto a council proposal by a councillor.
//! - `set_cooloff_period` - Specify cooling off period.
//! - `set_voting_period` - Specify voting period.
//! - `on_finalize` - Signature declaration that runs anything that needs to be done at the end of the block.
//!
//! ### Public Functions
//!
//! #### Council Motions
//!
//! - `is_councillor` - Check if a councillor is a member of the active council.
//!
//! #### Council Seats
//!
//! - `presentation_active` - Check if we're currently in a presentation period.
//! - `is_a_candidate` - Check if a specific account id is a registered candidate.
//! - `next_vote_from` - Determine the block when a vote can occur.
//! - `next_tally` - The block number when the tally for the next election will occur.
//!
//! #### Council Voting
//!
//! - `is_vetoed` - Check if a council proposal has been vetoed.
//! - `will_still_be_councillor_at` - Check each account id of the active council to determine what block number
//! they will still be active at.
//! - `is_councillor` - Check if a given account id is a councillor.
//! - `tally` - The count of the yay and nay votes associated with voting on a council proposal.
//!
//!
//! ### Snippet: Approve all candidates when additional empty seats are available
//!
//! This code snippet includes an `approve_all` public function that could be called by a signed account to approve
//! the eligibility of all candidates when there are empty council seats and when the tally for the next election
//! occurs at the current or a future block number.
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result};
//! use system::ensure_signed;
//! use srml_council::seats::{self as seats};
//!
//! pub trait Trait: seats::Trait {}
//!
//! decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!
//!	        // Approves all candidates.
//!	        pub fn approve_all(origin) -> Result {
//!	            let _origin = ensure_signed(origin)?;
//!
//!	            // Get the current block number
//!	            let current_block_number = <system::Module<T>>::block_number();
//!
//!	            // Get the number of seats that we want the council to have
//!	            let desired = <seats::Module<T>>::desired_seats() as usize;
//!
//!	            // Get the number of seats occupied by the current council.
//!	            let occupied = <seats::Module<T>>::active_council().len();
//!
//!	            // Get the appropriate block number to schedule the next tally.
//!	            let maybe_next_tally = <seats::Module<T>>::next_tally();
//!
//!	            assert!(desired > occupied, "Unable to approve all candidates when there are no empty seats");
//!
//!	            if let Some(next_tally_block_number) = <seats::Module<T>>::next_tally() {
//!	                if current_block_number <= next_tally_block_number {
//!	                    assert!(maybe_next_tally.is_some(),
//!	                        "Unable to approve all candidates when the block number of the next tally has past");
//!	                }
//!             }
//!
//!             Ok(())
//!         }
//!     }
//! }
//! # fn main() { }
//! ```
//!
//! ## Related Modules
//!
//! - [`System`](../srml_system/index.html)
//! - [`Support`](../srml_support/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

pub mod motions;
pub mod seats;
pub mod voting;

pub use crate::seats::{Event, Module, RawEvent, Trait, VoteIndex};

#[cfg(test)]
mod tests {
    // These re-exports are here for a reason, edit with care
    pub use super::*;
    pub use primitives::testing::{Digest, DigestItem, Header};
    pub use primitives::traits::{BlakeTwo256, IdentityLookup};
    pub use primitives::BuildStorage;
    pub use runtime_io::with_externalities;
    use srml_support::{impl_outer_dispatch, impl_outer_event, impl_outer_origin};
    pub use substrate_primitives::Blake2Hasher;
    pub use substrate_primitives::H256;
    pub use {motions, seats, voting};

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

    // Workaround for https://github.com/rust-lang/rust/issues/26925.  Remove when that issue is fixed.
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
        let mut t = system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap()
            .0;
        t.extend(
            balances::GenesisConfig::<Test> {
                transaction_base_fee: 0,
                transaction_byte_fee: 0,
                balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
                existential_deposit: 0,
                transfer_fee: 0,
                creation_fee: 0,
                vesting: vec![],
            }
            .build_storage()
            .unwrap()
            .0,
        );
        t.extend(
            democracy::GenesisConfig::<Test> {
                launch_period: 1,
                voting_period: 3,
                minimum_deposit: 1,
                public_delay: 0,
                max_lock_periods: 6,
            }
            .build_storage()
            .unwrap()
            .0,
        );
        t.extend(
            seats::GenesisConfig::<Test> {
                candidacy_bond: 9,
                voter_bond: 3,
                present_slash_per_voter: 1,
                carry_count: 2,
                inactive_grace_period: 1,
                active_council: if with_council {
                    vec![(1, 10), (2, 10), (3, 10)]
                } else {
                    vec![]
                },
                approval_voting_period: 4,
                presentation_duration: 2,
                desired_seats: 2,
                term_duration: 5,
            }
            .build_storage()
            .unwrap()
            .0,
        );
        t.extend(
            voting::GenesisConfig::<Test> {
                cooloff_period: 2,
                voting_period: 1,
                enact_delay_period: 0,
            }
            .build_storage()
            .unwrap()
            .0,
        );
        runtime_io::TestExternalities::new(t)
    }

    pub type System = system::Module<Test>;
    pub type Balances = balances::Module<Test>;
    pub type Democracy = democracy::Module<Test>;
    pub type Council = seats::Module<Test>;
    pub type CouncilVoting = voting::Module<Test>;
    pub type CouncilMotions = motions::Module<Test>;
}
