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

//! The Treasury: Keeps account of the taxed cash and handles its deployment.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(any(feature = "std", test))]
extern crate substrate_runtime_io as runtime_io;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_codec as codec;
#[cfg(test)]
extern crate substrate_primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_balances as balances;

use runtime_support::StorageValue;
use runtime_support::dispatch::Result;
use runtime_primitives::traits::OnFinalise;
use balances::OnMinted;

/// Our module's configuration trait. All our types and consts go in here. If the
/// module is dependent on specfiic other modules, then their configuration traits
/// should be added to our implied traits list.
/// 
/// `system::Trait` should always be included in our implied traits.
pub trait Trait: balances::Trait {
	/// The overarching event type. 
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

// The module declaration. This states the entry points that we handle. The
// macro looks after the marshalling of arguments and dispatch.
decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		// Put forward a suggestion for spending. A bond of 
		fn propose_spend(aux, amount: T::Balance, destination: T::AccountId) -> Result = 0;
	}

	// The priviledged entry points. These are provided to allow any governance modules in 
	// the runtime to be able to execute common functions. Unlike for `Call` there is no
	// auxilliary data to encode the sender (since there is no sender). Though still important
	// to ensure that these execute in reasonable time and space, they can do what would
	// otherwise be costly or unsafe operations.
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		// A priviledged call; in this case it resets our dummy value to something new.
		fn set_pot(new_pot: T::Balance) -> Result = 0;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum CouncilCall {
		// A priviledged call; in this case it resets our dummy value to something new.
		fn cancel_proposal(proposal_id: u32) -> Result = 0;

		// A priviledged call; in this case it resets our dummy value to something new.
		fn approve_proposal(proposal_id: u32) -> Result = 1;
	}
}

type ProposalIndex = u32;

#[derive(Encode, Decode, Clone, PartialEq, Eq)]
struct Proposal<AccountId, Balance> {
	proposer: AccountId,
	beneficiary: AccountId,
	value: Balance,
}

// NOTE: Perbill is parts-per-billion (i.e. multiply by this then divide by 1_000_000_000u32).

decl_storage! {
	trait Store for Module<T: Trait> as Treasury {
		// Total funds available to this module for spending.
		Pot get(pot): T::Balance;

		// Proportion of funds that should be bonded in order to place a proposal. An accepted
		// proposal gets these back. A rejected proposal doesn't.
		ProposalBondPerbill get(proposal_bond_perbill): u32;
		
		// Proportion of funds that should be bonded in order to place a proposal. An accepted
		// proposal gets these back. A rejected proposal doesn't.
		ProposalBondMinimum get(proposal_bond_minimum): T::Balance;

		// Proposals that have been made.
		Proposals get(proposals): map [ ProposalIndex => Proposal<T::AccountId, T::Balance> ];

		// Period between successive spends.
		SpendPeriod get(spend_period): T::BlockNumber;

		// Percentage of spare funds (if any) that are burnt per spend period.
		BurnPerbill get(burn_perbill): u32;
	}
}

/// Exported Event type that's generic over the configuration trait.
pub type Event<T> = RawEvent<
	<T as balances::Trait>::Balance,
	<T as system::Trait>::AccountId,
>;

/// An event in this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawEvent<Balance, AccountId> {
	/// Spent some funds.
	Spend(Balance, AccountId),
	/// Burnt some funds.
	Burn(Balance),
}

impl<B, A> From<RawEvent<B, A>> for () {
	fn from(_: RawEvent<B, A>) -> () { () }
}

impl<T: Trait> Module<T> {
	/// Deposit one of this module's events. This function doesn't change.
	// TODO: move into `decl_module` macro.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

	// Implement Calls/PrivCalls and add public immutables and private mutables.

	fn accumulate_dummy(_aux: &T::PublicAux, increase_by: T::Balance) -> Result {
		// Read the value of dummy from storage.
		let dummy = Self::dummy();
		// Will also work using the `::get` on the storage item type iself:
		// let dummy = <Dummy<T>>::get();

		// Calculate the new value.
		let new_dummy = dummy.map_or(increase_by, |dummy| dummy + increase_by);

		// Put the new value into storage.
		<Dummy<T>>::put(new_dummy);
		// Will also work with a reference:
		// <Dummy<T>>::put(&new_dummy);

		// Let's deposit an event to let the outside world this happened.
		Self::deposit_event(RawEvent::Dummy(increase_by));

		// All good.
		Ok(())
	}

	// Implementation of a priviledged call. This doesn't have an `aux` parameter because
	// it's not (directly) from an extrinsic, but rather the system as a whole has decided
	// to execute it. Different runtimes have different reasons for allow priviledged
	// calls to be executed - we don't need to care why. Because it's priviledged, we can
	// assume it's a one-off operation and substantial processing/storage/memort can be used
	// without worrying about gamability or attack scenarios.
	fn set_dummy(new_value: T::Balance) -> Result {
		// Put the new value into storage.
		<Dummy<T>>::put(new_value);

		// All good.
		Ok(())
	}
}

impl<T: Trait> OnMinted for Module<T> {
	fn on_minted(b: T::Balance) {
		<Pot<T>>::put(Self::pot() + b);
	}
}

impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(n: T::BlockNumber) {
		// Check to see if we should spend some funds!
		if 
		
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
/// The genesis block configuration type. This is a simple default-capable struct that
/// contains any fields with which this module can be configured at genesis time.
pub struct GenesisConfig<T: Trait> {
	/// A value with which to initialise the Dummy storage item.
	pub dummy: T::Balance,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			dummy: Default::default(),
		}
	}
}

// This expresses the specific key/value pairs that must be placed in storage in order
// to initialise the module and properly reflect the configuration.
// 
// Ideally this would re-use the `::put` logic in the storage item type for introducing
// the values into the `StorageMap`. That is not yet in place, though, so for now we
// do everything "manually", using `hash`, `::key()` and `.to_vec()` for the key and
// `.encode()` for the value.
#[cfg(any(feature = "std", test))]
impl<T: Trait> runtime_primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> ::std::result::Result<runtime_primitives::StorageMap, String> {
		use codec::Encode;
		Ok(map![
			Self::hash(<Dummy<T>>::key()).to_vec() => self.dummy.encode()
		])
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use runtime_primitives::BuildStorage;
	use runtime_primitives::traits::{BlakeTwo256};

	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
	use runtime_primitives::testing::{Digest, Header};

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type PublicAux = Self::AccountId;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = ();
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type AccountIndex = u64;
		type OnFreeBalanceZero = ();
		type EnsureAccountLiquid = ();
		type Event = ();
	}
	impl Trait for Test {
		type Event = ();
	}
	type Treasury = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<KeccakHasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		t.extend(balances::GenesisConfig::<Test>::default().build_storage().unwrap());
		t.extend(GenesisConfig::<Test>{
			dummy: 42,
		}.build_storage().unwrap());
		t.into()
	}

	#[test]
	fn it_works() {
		with_externalities(&mut new_test_ext(), || {
			// Check that GenesisBuilder works properly.
			assert_eq!(Treasury::dummy(), Some(42));

			// Check that accumulate works when we have Some value in Dummy already.
			assert_ok!(Treasury::accumulate_dummy(27.into()));
			assert_eq!(Treasury::dummy(), Some(69));
			
			// Check that finalising the block removes Dummy from storage.
			<Treasury as OnFinalise>::on_finalise();
			assert_eq!(Treasury::dummy(), None);

			// Check that accumulate works when we Dummy has None in it.
			assert_ok!(Treasury::accumulate_dummy(42.into()));
			assert_eq!(Treasury::dummy(), Some(42));
		});
	}
}
