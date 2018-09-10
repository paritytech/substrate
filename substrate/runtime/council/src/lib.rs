// Copyright 2017 Parity Technologies (UK) Ltd.
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

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

extern crate integer_sqrt;
extern crate substrate_codec as codec;
#[macro_use] extern crate substrate_codec_derive;
extern crate substrate_primitives;
#[cfg(feature = "std")] extern crate substrate_keyring as keyring;
#[macro_use] extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_balances as balances;
extern crate substrate_runtime_democracy as democracy;
extern crate substrate_runtime_system as system;

#[cfg(feature = "std")]
use rstd::prelude::*;
#[cfg(feature = "std")]
use std::collections::HashMap;
#[cfg(feature = "std")]
use primitives::traits::As;
#[cfg(feature = "std")]
use substrate_runtime_support::StorageValue;

pub mod voting;
pub mod motions;
pub mod seats;

pub use seats::{Trait, Module, RawEvent, Event, VoteIndex};

#[cfg(feature = "std")]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: seats::Trait> {
	// for the voting onto the council
	pub candidacy_bond: T::Balance,
	pub voter_bond: T::Balance,
	pub present_slash_per_voter: T::Balance,
	pub carry_count: u32,
	pub active_council: Vec<(T::AccountId, T::BlockNumber)>,
	pub approval_voting_period: T::BlockNumber,
	pub presentation_duration: T::BlockNumber,
	pub desired_seats: u32,
	pub term_duration: T::BlockNumber,
	pub inactive_grace_period: T::BlockNumber,

	// for the council's votes.
	pub cooloff_period: T::BlockNumber,
	pub voting_period: T::BlockNumber,
}

#[cfg(feature = "std")]
impl<T: seats::Trait + voting::Trait + motions::Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			candidacy_bond: T::Balance::sa(9),
			voter_bond: T::Balance::sa(0),
			present_slash_per_voter: T::Balance::sa(1),
			carry_count: 2,
			inactive_grace_period: T::BlockNumber::sa(1),
			active_council: vec![],
			approval_voting_period: T::BlockNumber::sa(1000),
			presentation_duration: T::BlockNumber::sa(1000),
			desired_seats: 0,
			term_duration: T::BlockNumber::sa(5),
			cooloff_period: T::BlockNumber::sa(1000),
			voting_period: T::BlockNumber::sa(3),
		}
	}
}

#[cfg(feature = "std")]
impl<T: seats::Trait + voting::Trait + motions::Trait> primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> ::std::result::Result<HashMap<Vec<u8>, Vec<u8>>, String> {
		use codec::Encode;

		Ok(map![
			Self::hash(<seats::CandidacyBond<T>>::key()).to_vec() => self.candidacy_bond.encode(),
			Self::hash(<seats::VotingBond<T>>::key()).to_vec() => self.voter_bond.encode(),
			Self::hash(<seats::PresentSlashPerVoter<T>>::key()).to_vec() => self.present_slash_per_voter.encode(),
			Self::hash(<seats::CarryCount<T>>::key()).to_vec() => self.carry_count.encode(),
			Self::hash(<seats::PresentationDuration<T>>::key()).to_vec() => self.presentation_duration.encode(),
			Self::hash(<seats::VotingPeriod<T>>::key()).to_vec() => self.approval_voting_period.encode(),
			Self::hash(<seats::TermDuration<T>>::key()).to_vec() => self.term_duration.encode(),
			Self::hash(<seats::DesiredSeats<T>>::key()).to_vec() => self.desired_seats.encode(),
			Self::hash(<seats::InactiveGracePeriod<T>>::key()).to_vec() => self.inactive_grace_period.encode(),
			Self::hash(<seats::ActiveCouncil<T>>::key()).to_vec() => self.active_council.encode(),

			Self::hash(<voting::CooloffPeriod<T>>::key()).to_vec() => self.cooloff_period.encode(),
			Self::hash(<voting::VotingPeriod<T>>::key()).to_vec() => self.voting_period.encode(),
			Self::hash(<voting::Proposals<T>>::key()).to_vec() => vec![0u8; 0].encode()
		])
	}
}

#[cfg(test)]
mod tests {
	// These re-exports are here for a reason, edit with care
	pub use super::*;
	pub use runtime_io::with_externalities;
	pub use substrate_primitives::H256;
	pub use primitives::BuildStorage;
	pub use primitives::traits::{BlakeTwo256};
	pub use primitives::testing::{Digest, Header};
	pub use substrate_primitives::KeccakHasher;
	pub use {seats, motions, voting};

	impl_outer_origin! {
		pub enum Origin for Test {
			motions
		}
	}

	impl_outer_event! {
		pub enum Event for Test {
			balances, democracy, seats, voting, motions
		}
	}

	impl_outer_dispatch! {
		pub enum Call where origin: Origin {
			Balances,
			Democracy,
		}
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = Event;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type AccountIndex = u64;
		type OnFreeBalanceZero = ();
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

	pub fn new_test_ext(with_council: bool) -> runtime_io::TestExternalities<KeccakHasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(balances::GenesisConfig::<Test>{
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			existential_deposit: 0,
			transfer_fee: 0,
			creation_fee: 0,
			reclaim_rebate: 0,
		}.build_storage().unwrap());
		t.extend(democracy::GenesisConfig::<Test>{
			launch_period: 1,
			voting_period: 3,
			minimum_deposit: 1,
		}.build_storage().unwrap());
		t.extend(GenesisConfig::<Test>{
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
			cooloff_period: 2,
			voting_period: 1,
		}.build_storage().unwrap());
		t.into()
	}

	pub type System = system::Module<Test>;
	pub type Balances = balances::Module<Test>;
	pub type Democracy = democracy::Module<Test>;
	pub type Council = seats::Module<Test>;
	pub type CouncilVoting = voting::Module<Test>;
	pub type CouncilMotions = motions::Module<Test>;
}