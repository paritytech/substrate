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

//! Timestamp manager: provides means to find out the current time.
//!
//! It is expected that the timestamp is set by the validator in the
//! beginning of each block, typically one of the first extrinsics. The timestamp
//! can be set only once per block and must be set each block.
//!
//! Note, that there might be a constraint on how much time must pass
//! before setting the new timestamp, specified by the `tim:block_period`
//! storage entry.
//!
//! # Interaction with the system
//!
//! ## Finalization
//!
//! This module should be hooked up to the finalization routine.
//!

#![cfg_attr(not(feature = "std"), no_std)]

extern crate sr_std as rstd;

#[macro_use]
extern crate srml_support as runtime_support;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
extern crate substrate_primitives;
#[cfg(test)]
extern crate sr_io as runtime_io;
extern crate sr_primitives as runtime_primitives;
extern crate srml_system as system;
extern crate srml_consensus as consensus;
extern crate parity_codec as codec;

use runtime_support::{StorageValue, Parameter};
use runtime_support::dispatch::Result;
use runtime_primitives::traits::{As, OnFinalise, SimpleArithmetic, Zero};
use system::ensure_inherent;
use rstd::ops::{Mul, Div};


pub trait Trait: consensus::Trait + system::Trait {
	/// The position of the required timestamp-set extrinsic.
	const TIMESTAMP_SET_POSITION: u32;

	/// Type used for expressing timestamp.
	type Moment: Parameter + Default + SimpleArithmetic + Mul<Self::BlockNumber, Output = Self::Moment> + Div<Self::BlockNumber, Output = Self::Moment>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn set(origin, now: T::Moment) -> Result;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Timestamp {
		/// Current time for the current block.
		pub Now get(now) build(|_| T::Moment::sa(0)): T::Moment;
		/// The minimum (and advised) period between blocks.
		pub BlockPeriod get(block_period) config(period): T::Moment = T::Moment::sa(5);

		/// Did the timestamp get updated in this block?
		DidUpdate: bool;
	}
}

impl<T: Trait> Module<T> {

	/// Get the current time for the current block.
	///
	/// NOTE: if this function is called prior the setting the timestamp,
	/// it will return the timestamp of the previous block.
	pub fn get() -> T::Moment {
		Self::now()
	}

	/// Set the current time.
	///
	/// Extrinsic with this call should be placed at the specific position in the each block
	/// (specified by the Trait::TIMESTAMP_SET_POSITION) typically at the start of the each block.
	/// This call should be invoked exactly once per block. It will panic at the finalization phase,
	/// if this call hasn't been invoked by that time.
	///
	/// The timestamp should be greater than the previous one by the amount specified by `block_period`.
	fn set(origin: T::Origin, now: T::Moment) -> Result {
		ensure_inherent(origin)?;
		assert!(!<Self as Store>::DidUpdate::exists(), "Timestamp must be updated only once in the block");
		assert!(
			<system::Module<T>>::extrinsic_index() == Some(T::TIMESTAMP_SET_POSITION),
			"Timestamp extrinsic must be at position {} in the block",
			T::TIMESTAMP_SET_POSITION
		);
		assert!(
			Self::now().is_zero() || now >= Self::now() + Self::block_period(),
			"Timestamp must increment by at least <BlockPeriod> between sequential blocks"
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

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::{with_externalities, TestExternalities};
	use substrate_primitives::H256;
	use runtime_primitives::BuildStorage;
	use runtime_primitives::traits::BlakeTwo256;
	use runtime_primitives::testing::{Digest, DigestItem, Header};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	#[derive(Clone, Eq, PartialEq)]
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
		type Event = ();
		type Log = DigestItem;
	}
	impl consensus::Trait for Test {
		const NOTE_OFFLINE_POSITION: u32 = 1;
		type Log = DigestItem;
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

		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::dispatch(Call::set(69), Origin::INHERENT));
			assert_eq!(Timestamp::now(), 69);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must be updated only once in the block")]
	fn double_timestamp_should_fail() {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test> { period: 5 }.build_storage().unwrap());

		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::dispatch(Call::set(69), Origin::INHERENT));
			let _ = Timestamp::dispatch(Call::set(70), Origin::INHERENT);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must increment by at least <BlockPeriod> between sequential blocks")]
	fn block_period_is_enforced() {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(GenesisConfig::<Test> { period: 5 }.build_storage().unwrap());

		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			let _ = Timestamp::dispatch(Call::set(46), Origin::INHERENT);
		});
	}
}
