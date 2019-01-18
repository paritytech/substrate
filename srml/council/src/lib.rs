// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Council system: Handles the voting in and maintenance of council members.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

extern crate parity_codec as codec;
#[macro_use] extern crate parity_codec_derive;
extern crate substrate_primitives;
#[cfg_attr(not(feature = "std"), macro_use)]
extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
#[macro_use] extern crate srml_support;
extern crate sr_primitives as primitives;
extern crate srml_balances as balances;
extern crate srml_democracy as democracy;
extern crate srml_system as system;

pub mod voting;
pub mod motions;
pub mod seats;

pub use seats::{Trait, Module, RawEvent, Event, VoteIndex};

#[cfg(test)]
mod tests {
	// These re-exports are here for a reason, edit with care
	pub use super::*;
	pub use runtime_io::with_externalities;
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
		type Lookup = IdentityLookup<u64>;
		type Header = Header;
		type Event = Event;
		type Log = DigestItem;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type EnsureAccountLiquid = ();
		type Event = Event;
	}
	impl democracy::Trait for Test {
		type Proposal = Call;
		type Event = Event;
	}
	impl seats::Trait for Test {
		type Event = Event;
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
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			existential_deposit: 0,
			transfer_fee: 0,
			creation_fee: 0,
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
