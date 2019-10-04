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

//! # Utility Module
//! A module full of useful helpers for practical chain management.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use support::{decl_module, decl_event, Parameter};
use system::ensure_root;
use sr_primitives::{
	traits::{Dispatchable, DispatchResult}, weights::SimpleDispatchInfo
};

/// Configuration trait.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin>;
}

pub type DispatchResultOf<T> = DispatchResult<<<T as Trait>::Call as Dispatchable>::Error>;

decl_event!(
	/// Events type.
	pub enum Event<T> where
		DispatchResult = DispatchResultOf<T>,
	{
		BatchExecuted(Vec<DispatchResult>),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Send a batch of dispatch calls (only root).
		#[weight = SimpleDispatchInfo::FreeOperational]
		fn batch(origin, calls: Vec<<T as Trait>::Call>) {
			ensure_root(origin)?;
			let results = calls.into_iter()
				.map(|call| call.dispatch(system::RawOrigin::Root.into()))
				.collect::<Vec<_>>();
			Self::deposit_event(RawEvent::BatchExecuted(results));
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use support::{assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch};
	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sr_primitives::{
		Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			balances::Balances,
			utility::Utility,
		}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
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
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
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
		pub const TransactionBaseFee: u64 = 0;
		pub const TransactionByteFee: u64 = 0;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = ();
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
	impl Trait for Test {
		type Event = ();
		type Call = Call;
	}
	type Balances = balances::Module<Test>;
	type Utility = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		balances::GenesisConfig::<Test> {
			balances: vec![(1, 10), (2, 0)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn batch_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Utility::batch(Origin::signed(1), vec![
				Call::Balances(balances::Call::force_transfer(1, 2, 5)),
				Call::Balances(balances::Call::force_transfer(1, 2, 5))
			]), "RequireRootOrigin");
			assert_ok!(Utility::batch(Origin::ROOT, vec![
				Call::Balances(balances::Call::force_transfer(1, 2, 5)),
				Call::Balances(balances::Call::force_transfer(1, 2, 5))
			]));
			assert_eq!(Balances::free_balance(1), 0);
			assert_eq!(Balances::free_balance(2), 10);
		});
	}
}
