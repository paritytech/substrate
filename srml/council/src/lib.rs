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
#![recursion_limit="128"]

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
	use srml_support::traits::Get;
	pub use primitives::{H256, Blake2Hasher, u32_trait::{_1, _2, _3, _4}};
	pub use sr_primitives::traits::{BlakeTwo256, IdentityLookup};
	pub use sr_primitives::testing::{Digest, DigestItem, Header};
	pub use sr_primitives::Perbill;
	pub use {seats, motions};
	use std::cell::RefCell;

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

	thread_local! {
		static VOTER_BOND: RefCell<u64> = RefCell::new(0);
		static VOTING_FEE: RefCell<u64> = RefCell::new(0);
		static PRESENT_SLASH_PER_VOTER: RefCell<u64> = RefCell::new(0);
		static DECAY_RATIO: RefCell<u32> = RefCell::new(0);
	}

	pub struct VotingBond;
	impl Get<u64> for VotingBond {
		fn get() -> u64 { VOTER_BOND.with(|v| *v.borrow()) }
	}

	pub struct VotingFee;
	impl Get<u64> for VotingFee {
		fn get() -> u64 { VOTING_FEE.with(|v| *v.borrow()) }
	}

	pub struct PresentSlashPerVoter;
	impl Get<u64> for PresentSlashPerVoter {
		fn get() -> u64 { PRESENT_SLASH_PER_VOTER.with(|v| *v.borrow()) }
	}

	pub struct DecayRatio;
	impl Get<u32> for DecayRatio {
		fn get() -> u32 { DECAY_RATIO.with(|v| *v.borrow()) }
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
		pub const TransactionBaseFee: u64 = 1;
		pub const TransactionByteFee: u64 = 0;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnNewAccount = ();
		type OnFreeBalanceZero = ();
		type Event = Event;
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = ();
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
	parameter_types! {
		pub const CandidacyBond: u64 = 3;
		pub const CarryCount: u32 = 2;
		pub const InactiveGracePeriod: u32 = 1;
		pub const CouncilVotingPeriod: u64 = 4;
	}
	impl seats::Trait for Test {
		type Event = Event;
		type BadPresentation = ();
		type BadReaper = ();
		type BadVoterIndex = ();
		type LoserCandidate = ();
		type OnMembersChanged = CouncilMotions;
		type CandidacyBond = CandidacyBond;
		type VotingBond = VotingBond;
		type VotingFee = VotingFee;
		type PresentSlashPerVoter = PresentSlashPerVoter;
		type CarryCount = CarryCount;
		type InactiveGracePeriod = InactiveGracePeriod;
		type CouncilVotingPeriod = CouncilVotingPeriod;
		type DecayRatio = DecayRatio;
	}
	impl motions::Trait for Test {
		type Origin = Origin;
		type Proposal = Call;
		type Event = Event;
	}

	pub struct ExtBuilder {
		balance_factor: u64,
		decay_ratio: u32,
		voting_fee: u64,
		voter_bond: u64,
		bad_presentation_punishment: u64,
		with_council: bool,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				balance_factor: 1,
				decay_ratio: 24,
				voting_fee: 0,
				voter_bond: 0,
				bad_presentation_punishment: 1,
				with_council: false,
			}
		}
	}

	impl ExtBuilder {
		pub fn with_council(mut self, council: bool) -> Self {
			self.with_council = council;
			self
		}
		pub fn balance_factor(mut self, factor: u64) -> Self {
			self.balance_factor = factor;
			self
		}
		pub fn decay_ratio(mut self, ratio: u32) -> Self {
			self.decay_ratio = ratio;
			self
		}
		pub fn voting_fee(mut self, fee: u64) -> Self {
			self.voting_fee = fee;
			self
		}
		pub fn bad_presentation_punishment(mut self, fee: u64) -> Self {
			self.bad_presentation_punishment = fee;
			self
		}
		pub fn voter_bond(mut self, fee: u64) -> Self {
			self.voter_bond = fee;
			self
		}
		pub fn set_associated_consts(&self) {
			VOTER_BOND.with(|v| *v.borrow_mut() = self.voter_bond);
			VOTING_FEE.with(|v| *v.borrow_mut() = self.voting_fee);
			PRESENT_SLASH_PER_VOTER.with(|v| *v.borrow_mut() = self.bad_presentation_punishment);
			DECAY_RATIO.with(|v| *v.borrow_mut() = self.decay_ratio);
		}
		pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
			self.set_associated_consts();
			let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
			balances::GenesisConfig::<Test>{
				balances: vec![
					(1, 10 * self.balance_factor),
					(2, 20 * self.balance_factor),
					(3, 30 * self.balance_factor),
					(4, 40 * self.balance_factor),
					(5, 50 * self.balance_factor),
					(6, 60 * self.balance_factor)
				],
				vesting: vec![],
			}.assimilate_storage(&mut t).unwrap();
			seats::GenesisConfig::<Test> {
				active_council: if self.with_council { vec![
					(1, 10),
					(2, 10),
					(3, 10)
				] } else { vec![] },
				desired_seats: 2,
				presentation_duration: 2,
				term_duration: 5,
			}.assimilate_storage(&mut t).unwrap();
			runtime_io::TestExternalities::new(t)
		}
	}

	pub type System = system::Module<Test>;
	pub type Balances = balances::Module<Test>;
	pub type Democracy = democracy::Module<Test>;
	pub type Council = seats::Module<Test>;
	pub type CouncilMotions = motions::Module<Test>;
}
