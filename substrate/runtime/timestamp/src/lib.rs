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

//! Timestamp manager: just handles the current timestamp.

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

#[cfg(test)]
extern crate substrate_primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_codec as codec;

use runtime_support::{StorageValue, Parameter};
use runtime_support::dispatch::Result;
use runtime_primitives::traits::{OnFinalise, MaybeEmpty, SimpleArithmetic, As, Zero};

pub trait Trait: consensus::Trait where
	<Self as system::Trait>::PublicAux: MaybeEmpty
{
	// the position of the required timestamp-set extrinsic.
	const TIMESTAMP_SET_POSITION: u32;

	type Moment: Parameter + Default + SimpleArithmetic + As<Self::BlockNumber>;
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn set(aux, now: T::Moment) -> Result;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Timestamp {
		pub Now get(now): required T::Moment;
		/// The minimum (and advised) period between blocks.
		pub BlockPeriod get(block_period): required T::Moment;

		/// Did the timestamp get updated in this block?
		DidUpdate: default bool;
	}
}

impl<T: Trait> Module<T> {
	pub fn get() -> T::Moment {
		Self::now()
	}

	/// Set the current time.
	fn set(aux: &T::PublicAux, now: T::Moment) -> Result {
		assert!(aux.is_empty());
		assert!(!<Self as Store>::DidUpdate::exists(), "Timestamp must be updated only once in the block");
		assert!(
			<system::Module<T>>::extrinsic_index() == Some(T::TIMESTAMP_SET_POSITION),
			"Timestamp extrinsic must be at position {} in the block",
			T::TIMESTAMP_SET_POSITION
		);
		assert!(
			Self::now().is_zero() || now >= Self::now() + Self::block_period(),
			"Timestamp but increment by at least <BlockPeriod> between sequential blocks"
		);
		<Self as Store>::Now::put(now);
		<Self as Store>::DidUpdate::put(true);
		Ok(())
	}

	/// Set the timestamp to something in particular. Only used for tests.
	#[cfg(any(feature = "std", test))]
	pub fn set_timestamp(now: T::Moment) {
		<Self as Store>::Now::put(now);
	}
}

impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(_n: T::BlockNumber) {
		assert!(<Self as Store>::DidUpdate::take(), "Timestamp must be updated once in the block");
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub period: T::Moment,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			period: T::Moment::sa(5),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> runtime_primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> ::std::result::Result<runtime_primitives::StorageMap, String> {
		use codec::Encode;
		Ok(map![
			Self::hash(<BlockPeriod<T>>::key()).to_vec() => self.period.encode(),
			Self::hash(<Now<T>>::key()).to_vec() => T::Moment::sa(0).encode()
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
	use runtime_primitives::testing::{Digest, Header};

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
	impl consensus::Trait for Test {
		const NOTE_OFFLINE_POSITION: u32 = 1;
		type Log = u64;
		type SessionKey = u64;
		type OnOfflineValidator = ();
	}
	impl Trait for Test {
		const TIMESTAMP_SET_POSITION: u32 = 0;
		type Moment = u64;
	}
	type Timestamp = Module<Test>;

	#[test]
	fn timestamp_works() {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test> { period: 0 }.build_storage().unwrap());
		let mut t = runtime_io::TestExternalities::from(t);
		with_externalities(&mut t, || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::aux_dispatch(Call::set(69), &0));
			assert_eq!(Timestamp::now(), 69);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must be updated only once in the block")]
	fn double_timestamp_should_fail() {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test> { period: 5 }.build_storage().unwrap());
		let mut t = runtime_io::TestExternalities::from(t);
		with_externalities(&mut t, || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::aux_dispatch(Call::set(69), &0));
			let _ = Timestamp::aux_dispatch(Call::set(70), &0);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp but increment by at least <BlockPeriod> between sequential blocks")]
	fn block_period_is_enforced() {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test> { period: 5 }.build_storage().unwrap());
		let mut t = runtime_io::TestExternalities::from(t);
		with_externalities(&mut t, || {
			Timestamp::set_timestamp(42);
			let _ = Timestamp::aux_dispatch(Call::set(46), &0);
		});
	}
}
