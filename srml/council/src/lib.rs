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

//! # Council System Module
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! Council system: Handles the voting in and maintenance of council members.
//!
//! ## Overview
//!
//! The Council system module provides functionality for different voting systems, including:
//!
//! * Council Motions
//! * Council Voting
//!
//! To use it in your runtime, you need to implement the council [`Trait`](./trait.Trait.html).
//!
//! The supported dispatchable functions are documented in the [`Call`](./enum.Call.html) enum.
//!
//! ### Terminology
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! * **Councillor** A councillor is a countable stakeholder. They may vote on a council proposal during the voting period if they did not create the proposal.
//!
//! #### Council proposals
//!
//! * **Council motion:** A mechanism used enact an outer `Call` dispatch (of type `Proposal`) from a council origin.
//! * **Council motion vote:** Allows an arbitrary number of councillors (other than the councillor that proposed the motion) to vote and initiate a call. 
//! * **Council origin:** The council origin is the Council (not Root) and contains the council motion mechanism. It has different mechanics to other origins. 
//! * **Council proposal validity prerequisites:** A council proposal is valid when:
//!   * Submitted by a councillor.
//!   * Not a duplicate proposal.
//!   * Not vetoed.
//!   * Council term does not expire before the proposals' voting period has lapsed.
//! * **Council term:** **TODO**
//! * **Council proposal creation:** TODO
//! * **Council proposal creation storage** A council proposal after being deemed valid is stored as follows:
//!   * Proposals' storage vector is updated with a tuple containing the proposal's hash and the expiry block number of its voting period.
//!   * Proposals' hash is mapped to the proposals' value in storage using `ProposalOf`.
//!   * Proposals' hash is mapped to a vector of account ids that have voted the proposal in storage using `ProposalVoters`. Initially the account ID of the councillor that created the proposal is added to the vector.
//!   * Councillor's vote storage tuple `CouncilVoteOf` is updated with a mapping between the proposal's hash and the councillor's account id. Initially the councillor that created the proposal is added with a vote of yay.
//! * **Council proposal vote storage** A council proposal vote that occurs after council proposal creation is stored as follows:
//!   * `ProposalVoters` storage vector that contains account IDs that have voted for the proposal's hash is updated with the Councillor's new vote.
//!   * Councillor's vote storage tuple `CouncilVoteOf` is updated with a mapping between a tuple containing the proposal's hash and the councillor's account id, and the Councillor's new vote. 
//!	  * `Voting` storage mapping is updated with the Councillor's vote.
//! 	* Note that `Voting` maps the proposal's hash to a tuple containing the corresponding proposal's index, vote threshold, and vectors of both yay and nay voter account IDs. 
//! * **Council proposal voting rules**
//!   * Duplicate votes from the same councillor are ignored.
//!   * Councillors may swap their vote from yay to nay and vice versa.
//! * **Council proposal vote threshold**
//!   * A council proposal that is created with a threshold level of one is voted upon and approved by the councillor that created it, and then executed.
//!	  * A council proposal with a threshold level of more than one is added to the `Voting` storage mapping.
//!
//! #### Council XXXX
//! * **Council voting:**
//!   * The vote function in srml/council/src/voting.rs is for the Council Voting as a body regarding tabling referenda.
//!
//! ### Goals
//!
//! The council system in Substrate is designed to make the following possible:
//!
//! TODO
//!
//! ### Scenarios
//!
//! #### 
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! TODO
//!
//! Please refer to the [`Call`](./enum.Call.html) enum and its associated variants for documentation on each function.
//!
//! ### Public Functions
//!
//! TODO
//!
//! Please refer to the [`Module`](./struct.Module.html) struct for details on publicly available functions.
//!
//! ## Usage
//!
//! The following example shows how to use the Council module in your runtime by exposing public functions to:
//!
//! TODO
//!
//! ### Prerequisites
//!
//! Import the Council module and types and derive your runtime's configuration traits from the Council module trait.
//!
//! ### Simple Code Snippet
//!
//! TODO
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
