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
//!
//! The Council module provides tools to manage the council and proposals. The main components are:
//!
//! - **Council Seats:** Election of councillors.
//! 	- [`seats::Trait`](./seats/trait.Trait.html)
//! 	- [`Call`](./seats/enum.Call.html)
//! 	- [`Module`](./seats/struct.Module.html)
//! - **Council Motions:** Voting as a body to dispatch calls from the `Council` origin.
//! 	- [`motions::Trait`](./motions/trait.Trait.html)
//! 	- [`Call`](./motions/enum.Call.html)
//! 	- [`Module`](./motions/struct.Module.html)
//! - **Council Voting:** Proposals sent to the [Democracy module](../srml_democracy/index.html) for referenda.
//! 	- [`voting::Trait`](./voting/trait.Trait.html)
//! 	- [`Call`](./voting/enum.Call.html)
//! 	- [`Module`](./voting/struct.Module.html)
//!
//! ## Overview
//!
//! The Council module provides functionality to handle:
//!
//! - Voting in and maintenance of council members.
//! - Proposing, vetoing, and passing of motions.
//!
//! The council is an on-chain entity comprised of a set of account IDs, with the role of representing
//! passive stakeholders. Its primary tasks are to propose sensible referenda and thwart any uncontroversially
//! dangerous or malicious referenda.
//!
//! ### Terminology
//!
//! #### Council Motions (motions.rs)
//!
//! _Motions_ handle internal proposals that are only proposed and voted upon by _councillors_.
//! Each proposal has a minimum threshold of yay votes that it needs to gain to be enacted.
//!
//! - **Council motion:** A mechanism used to enact a proposal.
//! - **Proposal:** A submission by a councillor. An initial vote of yay from that councillor is applied.
//! - **Vote:** A vote of yay or nay from a councillor on a single proposal. Councillors may change their vote but a
//!   duplicate vote will return an error.
//!
//! Upon each vote, if the threshold is reached, the proposal is dispatched from the `Council` origin. Similarly,
//! if the number of nay votes is high enough such that it could not pass even if all other councillors
//! (including those who have not voted) voted yay, the proposal is dropped.
//!
//! Note that a council motion has a special origin type, [`seats::Origin`](./motions/enum.Origin.html), that limits
//! which calls can be effectively dispatched.
//!
//! #### Council Voting (voting.rs)
//!
//! _Voting_ handles councillor proposing and voting. Unlike motions, if a proposal is approved,
//! it is elevated to the [Democracy module](../srml_democracy/index.html) as a referendum.
//!
//! - **Proposal validity:** A council proposal is valid when it's unique, hasn't yet been vetoed, and
//! when the proposing councillor's term doesn't expire before the block number when the proposal's voting period ends.
//! A proposal is a generic type that can be _dispatched_ (similar to variants of the `Call` enum in each module).
//! - **Proposal postponement:** Councillors may postpone a council proposal from being approved or rejected.
//! Postponement is equivalent to a veto, which only lasts for the cooloff period.
//! - **Cooloff period:** Period, in blocks, for which a veto is in effect.
//! - **Referendum:** The means of public voting on a proposal.
//! - **Veto:** A council member may veto any council proposal that exists. A vetoed proposal that's valid is set
//! aside for a cooloff period. The vetoer cannot re-veto or propose the proposal again until the veto expires.
//! - **Elevation:** A referendum can be elevated from the council to a referendum. This means it has
//! been passed to the Democracy module for a public vote.
//! - **Referendum cancellation:** At the end of a given block we cancel all elevated referenda whose voting period
//! ends at that block and where the outcome of the vote tally was a unanimous vote to cancel the referendum.
//! - **Voting process to elevate a proposal:** At the end of a given block we tally votes for expiring referenda.
//! Referenda that are passed (yay votes are greater than nay votes plus abstainers) are sent to the Democracy
//! module for a public referendum. If there are no nay votes (abstention is acceptable), then the proposal is
//! tabled immediately. Otherwise, there will be a delay period. If the vote is unanimous, then the public
//! referendum will require a vote threshold of supermajority against to prevent it. Otherwise,
//! it is a simple majority vote. See [`VoteThreshold`](../srml_democracy/enum.VoteThreshold.html) in the
//! Democracy module for more details on how votes are approved.
//!
//! As opposed to motions, proposals executed through the Democracy module have the
//! root origin, which gives them the highest privilege.
//!
//! #### Council Seats (seats.rs)
//!
//! _Seats_ handles the selection of councillors. The selection of council seats is a circulating procedure,
//! regularly performing approval voting to accept a new council member and remove those whose period has ended.
//! Each tally (round of voting) is divided into two time periods:
//!
//!   - **Voting period:** In which any stakeholder can vote for any of the council candidates.
//!   - **Presentation period:** In which voting is no longer allowed and stakeholders can _present_ a candidate
//!   and claim that a particular candidate has won a seat.
//!
//! A tally is scheduled to execute based on the number of desired and free seats in the council.
//!
//! Both operations have associated bonds and fees that need to be paid based on the complexity of the transaction.
//! See [`set_approvals`](./seats/enum.Call.html#variant.set_approvals) and
//! [`submit_candidacy`](./seats/enum.Call.html#variant.submit_candidacy) for more information.
//!
//! Upon the end of the presentation period, the leaderboard is finalized and sorted based on the approval
//! weight of the _presented_ candidates.
//! Based on the configurations of the module, `N` top candidates in the leaderboard are immediately recognized
//! as councillors (where `N` is `desired_seats - active_council.len()`) and runners-up are kept in
//! the leaderboard as carry for the next tally to compete again. Similarly, councillors whose term has ended
//! are also removed.
//!
//! - **Vote index**: A counter indicating the number of tally rounds already applied.
//! - **Desired seats:** The number of seats on the council.
//! - **Candidacy bond:** Bond required to be a candidate. The bond is returned to all candidates at the end
//! of the tally if they have won the tally (i.e. have become a councillor).
//! - **Leaderboard:** A list of candidates and their respective votes in an election, ordered low to high.
//! - **Presentation:** The act of proposing a candidate for insertion into the leaderboard. Presenting is
//! `O(|number_of_voters|)`, so the presenter must be slashable and will be slashed for duplicate or invalid
//! presentations. Presentation is only allowed during the "presentation period," after voting has closed.
//! - **Voting bond:** Bond required to be permitted to vote. Must be held because many voting operations affect
//! storage. The bond is held to disincent abuse.
//! - **Voting:** Process of inserting approval votes into storage. Can be called by anyone, given she submits
//! an appropriate list of approvals. A bond is reserved from a voter until she retracts or gets reported.
//! - **Inactive voter**: A voter whose approvals are now invalid. Such voters can be _reaped_ by other voters
//!   after an `inactivity_grace_period` has passed from their last known activity.
//! - **Reaping process:** Voters may propose the removal of inactive voters, as explained above. If the claim is not
//! valid, the _reaper_ will be slashed and removed as a voter. Otherwise, the _reported_ voter is removed. A voter
//! always gets his or her bond back upon being removed (either through _reaping_ or _retracting_).
//!
//! ### Goals
//!
//! The Council module in Substrate is designed to make the following possible:
//!
//! - Create council proposals by councillors using the council motion mechanism.
//! - Validate council proposals.
//! - Tally votes of council proposals by councillors during the proposal's voting period.
//! - Veto (postpone) council proposals for a cooloff period through abstention by councillors.
//! - Elevate council proposals to start a referendum.
//! - Execute referenda once their vote tally reaches the vote threshold level of approval.
//! - Manage candidacy, including voting, term expiration, and punishment.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! The dispatchable functions in the Council module provide the functionality that councillors need.
//! See the `Call` enums from the Motions, Seats, and Voting modules for details on dispatchable functions.
//!
//! ### Public Functions
//!
//! The public functions provide the functionality for other modules to interact with the Council module.
//! See the `Module` structs from the Motions, Seats, and Voting modules for details on public functions.
//!
//! ## Usage
//!
//! ### Council Seats: Councillor Election Procedure
//!
//! A Council seat vote can proceed as follows:
//!
//! 1. Candidates submit themselves for candidacy.
//! 2. Voting occurs.
//! 3. Voting period ends and presentation period begins.
//! 4. Candidates are presented for the leaderboard.
//! 5. Presentation period ends, votes are tallied, and new council takes effect.
//! 6. Candidate list is cleared (except for a defined number of carries) and vote index increased.
//!
//! ### Council Votes: Proposal Elevation Procedure
//!
//! A council motion elevation would proceed as follows:
//!
//! 1. A councillor makes a proposal.
//! 2. Other councillors vote yay or nay or abstain.
//! 3. At the end of the voting period, the votes are tallied.
//! 4. If it has passed, then it will be sent to the Democracy module with the vote threshold parameter.
//!
//! ### Example
//!
//! This code snippet includes an `approve_all` public function that could be called to approve all
//! existing candidates, if a tally is scheduled to happen, without having to check the number of them.
//!
//! ```ignore
//! use srml_support::{decl_module, dispatch::Result};
//! use system::ensure_signed;
//! use srml_council::seats;
//!
//! pub trait Trait: seats::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!
//! 		pub fn approve_all(origin, vote_index: u32) -> Result {
//! 			// Get the appropriate block number to schedule the next tally.
//! 			let maybe_next_tally = <seats::Module<T>>::next_tally();
//!
//! 			if maybe_next_tally.is_some() {
//! 				// Create votes.
//! 				let candidate_count = <seats::Module<T>>::candidate_count();
//! 				let votes = vec![true; candidate_count as usize];
//!
//!					<seats::Module<T>>::set_approvals(origin, votes, vote_index)?;
//! 			}
//!
//!				// either way return `Ok`. You can change this and return an `Err` based on what you need.
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```
//!
//! ## Genesis Config
//!
//! The Council module depends on the `GenesisConfig`.
//!
//! - [Seats](./seats/struct.GenesisConfig.html)
//! - [Voting](./voting/struct.GenesisConfig.html)
//!
//! ## Related Modules
//!
//! - [Democracy](../srml_democracy/index.html)
//! - [Staking](../srml_staking/index.html)
//!
//! ## References
//!
//! - [Polkadot wiki](https://wiki.polkadot.network/en/latest/polkadot/learn/governance/) on governance.

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

	// Workaround for https://github.com/rust-lang/rust/issues/26925. Remove when sorted.
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
