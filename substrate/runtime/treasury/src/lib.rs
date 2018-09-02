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

#[cfg(test)]
extern crate substrate_primitives;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_balances as balances;
extern crate substrate_codec as codec;

use runtime_support::{StorageValue, Parameter};
use runtime_support::dispatch::Result;
use runtime_primitives::traits::{OnFinalise, MaybeEmpty, SimpleArithmetic, As, Zero};
use balances::OnMinted;

/// Our module's configuration trait. All our types and consts go in here.
pub trait Trait: balances::Trait {
	/// The overarching event type. 
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

// The module declaration. This states the entry points that we handle. The
// macro looks after the marshalling of arguments and dispatch.
decl_module! {
	pub struct Module<T: Trait>;

	// The unpriviledged entry points. Any account can call into these by signing and submitting
	// an extrinsic. Ensure that calls into each of these execute in a time, memory and
	// using storage space proportional to any costs paid for by the caller.
	//
	// The account that is calling this (i.e. the one that signed the extrinsic) is provided
	// via the `aux` argument, always first in each function call. As such functions must
	// always look like:
	// 
	// `fn foo(aux, bar: Bar, baz: Baz) -> Result = 0;`
	//
	// The `Result` is required as part of the syntax (and expands to the conventional dispatch
	// result of `Result<(), &'static str>`). The index after `=` must be unique within this
	// enum (the `PrivCall` enum is allowed to reuse indexes).
	// 
	// When you come to `impl` them later in the module, you must specify the full type for `aux`:
	//
	// `fn foo(aux: T::PublicAux, bar: Bar, baz: Baz) { ... }`
	//
	// This is your public interface. Be extremely careful.
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
	}

	// The priviledged entry points. These are provided to allow any governance modules in 
	// the runtime to be able to execute common functions. Unlike for `Call` there is no
	// auxilliary data to encode the sender (since there is no sender). Though still important
	// to ensure that these execute in reasonable time and space, they can do what would
	// otherwise be costly or unsafe operations.
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
	}
}

/// Exported Event type that's generic over the configuration trait.
// NOTE: External macro-fu expects this type to exist and be generic over
// the configuration trait.
pub type Event<T> = RawEvent<
	<T as balances::Trait>::Balance,
>;

/// An event in this module. Events are simple means of reporting specific conditions and
/// cursumstances that have happened that users, Dapps and/or chain explorers would find
/// interested and otherwise difficult to detect.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawEvent<B> {
	// Just a normal `enum`, here's a dummy event to ensure it compiles.
	/// Dummy event, just here so there's a generic type that's used.
	Dummy(B),
}

impl<A> From<RawEvent<B>> for () {
	fn from(_: RawEvent<B>) -> () { () }
}

decl_storage! {
	// A macro for the Storage trait, and its implementation, for this module.
	// This allows for type-safe usage of the Substrate storage database, so you can
	// keep things around between blocks.
	trait Store for Module<T: Trait> as Treasury {
		// TODO: Any storage declarations of the form:
		//   `pub? Name get(getter_name)? : [required | default]? Type;`
		// Note that there are two optional modifiers for the storage type declaration.
		// - `Foo: u32`:
		//   - `Foo::put(1); Foo::get()` returns `Some(1)`;
		//   - `Foo::kill(); Foo::get()` returns `None`.
		// - `Foo: required u32`:
		//   - `Foo::put(1); Foo::get()` returns `1`;
		//   - `Foo::kill(); Foo::get()` panics.
		// - `Foo: default u32`:
		//   - `Foo::put(1); Foo::get()` returns `1`;
		//   - `Foo::kill(); Foo::get()` returns `0` (u32::default()).
		// e.g. Foo: u32;
		// e.g. pub Bar get(bar): default map [ T::AccountId => Vec<(T::Balance, u64)> ];
		Dummy get(dummy): T::Balance;
	}
}

// The main implementation block for the module. Functions here fall into three broad
// categories:
// - Implementations of dispatch functions. The dispatch code generated by the module macro
// expects each of its functions to be implemented.
// - Public interface. These are functions that are `pub` and generally fall into inspector
// functions that do not write to storage and operation functions that do.
// - Private functions. These are your usual private utilities unavailable to other modules.
impl<T: Trait> Module<T> {
	/// Deposit one of this module's events.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

	// TODO: Implement Calls/PrivCalls and add public immutables and private mutables.
}

// The trait expresses what should happen when the block is finalised.
impl<T: Trait> OnFinalise for Module<T> {
	fn on_finalise() {
		// TODO: Anything that needs to be done at the end of the block. 
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
/// The genesis block configuration type. This is a simple default-capable struct that
/// contains any fields with which this module can be configured at genesis time.
pub struct GenesisConfig<T: Trait> {
	/// A dummy entry to ensure this is compilable.
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
	use runtime_primitives::traits::{HasPublicAux, BlakeTwo256};
	use runtime_primitives::testing::{Digest, Header};

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl system::Trait for Test {
		type PublicAux = u64;
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
		type Balance: u64;
		type AccountIndex: u64;
		type OnFreeBalanceZero: ();
		type EnsureAccountLiquid: ();
		type Event: ();
	}
	impl Trait for Test {
		type Event = ();
	}
	type Treasury = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<KeccakHasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(balances::GenesisConfig::<Test>{
			balances: vec![(0, 100)],
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			transfer_fee: 0,
			creation_fee: 0,
			reclaim_rebate: 0,
			existential_deposit: 0,
		}.build_storage().unwrap());
		t.extend(GenesisConfig::<Test>{
			dummy: 42,
		}.build_storage().unwrap());
		t.into()
	}

	#[test]
	fn it_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq(Treasury::dummy(), 42);
		});
	}
}
