// Copyright 2019 Parity Technologies (UK) Ltd.
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

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_core::TypeId;
use sp_core::blake2_256;
use frame_support::{decl_module, decl_event, decl_storage, Parameter};
use frame_support::weights::{
	SimpleDispatchInfo, GetDispatchInfo, ClassifyDispatch, WeighData, Weight, DispatchClass, PaysFee
};
use frame_system::{self as system, ensure_root, ensure_signed};
use sp_runtime::{DispatchError, DispatchResult, traits::{Dispatchable, AccountIdConversion}};

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo;
}

decl_storage! {
	trait Store for Module<T: Trait> as Utility {
		/// The ideal number of staking participants.
		pub ValidatorCount get(fn validator_count) config(): u32;
	}
}

decl_event!(
	/// Events type.
	pub enum Event {
		BatchExecuted(Vec<Result<(), DispatchError>>),
	}
);

/// Simple index-based pass through for the weight functions.
struct Passthrough<Call>(sp_std::marker::PhantomData<Call>);

impl<Call> Passthrough<Call> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo> WeighData<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn weigh_data(&self, (_, call): (&u16, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight + 10_000
	}
}
impl<Call: GetDispatchInfo> ClassifyDispatch<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn classify_dispatch(&self, (_, call): (&u16, &Box<Call>)) -> DispatchClass {
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo> PaysFee for Passthrough<Call> {
	fn pays_fee(&self) -> bool {
		true
	}
}

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedUtilityModuleId(u16);

impl TypeId for IndexedUtilityModuleId {
	const TYPE_ID: [u8; 4] = *b"suba";
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Send a batch of dispatch calls (only root).
		// TODO: Should also pass through the weights.
		// TODO: Should not be restricted to Root origin; should duplicate the origin for each.
		#[weight = SimpleDispatchInfo::FreeOperational]
		fn batch(origin, calls: Vec<<T as Trait>::Call>) {
			ensure_root(origin)?;
			let results = calls.into_iter()
				.map(|call| call.dispatch(frame_system::RawOrigin::Root.into()))
				.map(|res| res.map_err(Into::into))
				.collect::<Vec<_>>();
			Self::deposit_event(Event::BatchExecuted(results));
		}

		/// Send a call through an indexed pseudonym of the sender.
		#[weight = <Passthrough<<T as Trait>::Call>>::new()]
		fn as_sub(origin, index: u16, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let entropy = (b"modlpy/utilisuba", who, index).using_encoded(blake2_256);
			let pseudonym = T::AccountId::decode(&mut &entropy[..]).unwrap_or_default();
			call.dispatch(frame_system::RawOrigin::Signed(pseudonym).into())
		}
	}
}

impl<T: Trait> Module<T> {
	pub fn sub_account_id(who: T::AccountId, index: u16) -> T::AccountId {
		// the slightly odd order of having the index value have a sub account of `who` here
		// is to ensure that only the account id `who` is truncated, not the `index`.
		IndexedUtilityModuleId(index).into_sub_account(&who)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
		weights::Weight
	};
	use sp_core::H256;
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			pallet_balances::Balances,
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
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
	}
	impl Trait for Test {
		type Event = ();
		type Call = Call;
	}
	type Balances = pallet_balances::Module<Test>;
	type Utility = Module<Test>;

	use pallet_balances::Call as BalancesCall;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 10), (2, 0)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn as_sub_works() {
		new_test_ext().execute_with(|| {
			let sub_1_0 = Utility::sub_account_id(1, 0);
			assert_ok!(Balances::transfer(Origin::signed(1), sub_1_0, 5));
			assert_noop!(Utility::as_sub(
				Origin::signed(1),
				1,
				Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
			), "balance too low to send value");
			assert_ok!(Utility::as_sub(
				Origin::signed(1),
				0,
				Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
			));
			assert_eq!(Balances::free_balance(sub_1_0), 2);
			assert_eq!(Balances::free_balance(2), 3);
		});
	}

	#[test]
	fn batch_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 0);
			assert_noop!(
				Utility::batch(Origin::signed(1), vec![
					Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
					Call::Balances(BalancesCall::force_transfer(1, 2, 5))
				]),
				BadOrigin,
			);
			assert_ok!(Utility::batch(Origin::ROOT, vec![
				Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
				Call::Balances(BalancesCall::force_transfer(1, 2, 5))
			]));
			assert_eq!(Balances::free_balance(1), 0);
			assert_eq!(Balances::free_balance(2), 10);
		});
	}
}
