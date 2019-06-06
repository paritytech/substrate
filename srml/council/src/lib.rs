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

//! Council system: Handles the voting in and maintenance of council members.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod motions;
pub mod seats;

pub use crate::seats::{Trait, Module, RawEvent, Event, VoteIndex};

/// Trait for type that can handle incremental changes to a set of account IDs.
pub trait OnMembersChanged<AccountId> {
	/// A number of members `new` just joined the set and replaced some `old` ones.
	fn on_members_changed(new: &[AccountId], old: &[AccountId]);
}

impl<T> OnMembersChanged<T> for () {
	fn on_members_changed(_new: &[T], _old: &[T]) {}
}

#[cfg(test)]
mod tests {
	// These re-exports are here for a reason, edit with care
	pub use super::*;
	pub use runtime_io::with_externalities;
	use srml_support::{impl_outer_origin, impl_outer_event, impl_outer_dispatch, parameter_types};
	pub use substrate_primitives::{H256, Blake2Hasher, u32_trait::{_1, _2, _3, _4}};
	pub use primitives::{
		BuildStorage, traits::{BlakeTwo256, IdentityLookup}, testing::{Digest, DigestItem, Header}
	};
	pub use {seats, motions};

	impl_outer_origin! {
		pub enum Origin for Test {
			motions<T>
		}
	}

	impl_outer_event! {
		pub enum Event for Test {
			balances<T>, democracy<T>, seats<T>, motions<T>,
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
	parameter_types! {
		pub const LaunchPeriod: u64 = 1;
		pub const VotingPeriod: u64 = 3;
		pub const MinimumDeposit: u64 = 1;
		pub const EnactmentPeriod: u64 = 0;
		pub const CooloffPeriod: u64 = 2;
	}
	impl democracy::Trait for Test {
		type Proposal = Call;
		type Event = Event;
		type Currency = balances::Module<Self>;
		type EnactmentPeriod = EnactmentPeriod;
		type LaunchPeriod = LaunchPeriod;
		type EmergencyVotingPeriod = VotingPeriod;
		type VotingPeriod = VotingPeriod;
		type MinimumDeposit = MinimumDeposit;
		type ExternalOrigin = motions::EnsureProportionAtLeast<_1, _2, u64>;
		type ExternalMajorityOrigin = motions::EnsureProportionAtLeast<_2, _3, u64>;
		type EmergencyOrigin = motions::EnsureProportionAtLeast<_1, _1, u64>;
		type CancellationOrigin = motions::EnsureProportionAtLeast<_2, _3, u64>;
		type VetoOrigin = motions::EnsureMember<u64>;
		type CooloffPeriod = CooloffPeriod;
	}
	impl seats::Trait for Test {
		type Event = Event;
		type BadPresentation = ();
		type BadReaper = ();
		type OnMembersChanged = CouncilMotions;
	}
	impl motions::Trait for Test {
		type Origin = Origin;
		type Proposal = Call;
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
		t.extend(democracy::GenesisConfig::<Test>::default().build_storage().unwrap().0);
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
		runtime_io::TestExternalities::new(t)
	}

	pub type System = system::Module<Test>;
	pub type Balances = balances::Module<Test>;
	pub type Democracy = democracy::Module<Test>;
	pub type Council = seats::Module<Test>;
	pub type CouncilMotions = motions::Module<Test>;
}
