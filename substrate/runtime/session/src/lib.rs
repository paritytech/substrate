// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Session manager: is told the validators and allows them to manage their session keys for the
//! consensus module.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")] extern crate serde;

extern crate substrate_codec as codec;
extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
//use runtime_io::{twox_128, TestExternalities};
use primitives::{Zero, One, RefInto, Executable, Convert};
use runtime_support::{StorageValue, StorageMap};

pub trait Trait: consensus::Trait + system::Trait {
	type PublicAux: RefInto<Self::AccountId>;
	type Conversion: Convert<Self::AccountId, Self::SessionKey>;
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
		fn set_key(aux, key: T::SessionKey) = 0;
	}
	pub enum PrivCall {
		fn set_length(new: T::BlockNumber) = 0;
		fn force_new_session() = 1;
	}
}
decl_storage! {
	trait Store for Module<T: Trait>;

	// The current set of validators.
	pub Validators get(validators): b"ses:val" => required Vec<T::AccountId>;
	// Current length of the session.
	pub SessionLength get(length): b"ses:len" => required T::BlockNumber;
	// Current index of the session.
	pub CurrentIndex get(current_index): b"ses:ind" => required T::BlockNumber;

	// Block at which the session length last changed.
	LastLengthChange: b"ses:llc" => T::BlockNumber;
	// The next key for a given validator.
	NextKeyFor: b"ses:nxt:" => map [ T::AccountId => T::SessionKey ];
	// The next session length.
	NextSessionLength: b"ses:nln" => T::BlockNumber;
}

impl<T: Trait> Module<T> {
	/// The number of validators currently.
	pub fn validator_count() -> u32 {
		<Validators<T>>::get().len() as u32	// TODO: can probably optimised
	}

	/// The last length change, if there was one, zero if not.
	pub fn last_length_change() -> T::BlockNumber {
		<LastLengthChange<T>>::get().unwrap_or_else(T::BlockNumber::zero)
	}

	/// Sets the session key of `_validator` to `_key`. This doesn't take effect until the next
	/// session.
	fn set_key(aux: &T::PublicAux, key: T::SessionKey) {
		// set new value for next session
		<NextKeyFor<T>>::insert(RefInto::into(aux), key)
	}

	/// Set a new era length. Won't kick in until the next era change (at current length).
	fn set_length(new: T::BlockNumber) {
		<NextSessionLength<T>>::put(new);
	}

	/// Forces a new session.
	fn force_new_session() {
		Self::rotate_session();
	}

	// INTERNAL API (available to other runtime modules)

	/// Set the current set of validators.
	///
	/// Called by `staking::next_era()` only. `next_session` should be called after this in order to
	/// update the session keys to the next validator set.
	pub fn set_validators(new: &[T::AccountId]) {
		<Validators<T>>::put(&new.to_vec());			// TODO: optimise.
		<consensus::Module<T>>::set_authorities(
			&new.iter().cloned().map(T::Conversion::convert).collect::<Vec<_>>()
		);
	}

	/// Hook to be called after transaction processing.
	pub fn check_rotate_session() {
		// do this last, after the staking system has had chance to switch out the authorities for the
		// new set.
		// check block number and call next_session if necessary.
		let block_number = <system::Module<T>>::block_number();
		if ((block_number - Self::last_length_change()) % Self::length()).is_zero() {
			Self::rotate_session();
		}
	}

	/// Move onto next session: register the new authority set.
	pub fn rotate_session() {
		// Increment current session index.
		<CurrentIndex<T>>::put(<CurrentIndex<T>>::get() + One::one());

		// Enact era length change.
		if let Some(next_len) = <NextSessionLength<T>>::take() {
			let block_number = <system::Module<T>>::block_number();
			<SessionLength<T>>::put(next_len);
			<LastLengthChange<T>>::put(block_number);
		}

		// Update any changes in session keys.
		Self::validators().iter().enumerate().for_each(|(i, v)| {
			if let Some(n) = <NextKeyFor<T>>::take(v) {
				<consensus::Module<T>>::set_authority(i as u32, &n);
			}
		});
	}
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
		Self::check_rotate_session();
	}
}
/*
#[cfg(any(feature = "std", test))]
pub mod testing {
	use super::*;
	use runtime_io::{twox_128, TestExternalities};
	use codec::{Joiner, KeyedVec};
	use keyring::Keyring::*;
	use runtime::system;

	pub fn externalities(session_length: u64) -> TestExternalities {
		let three = [3u8; 32];

		let extras: TestExternalities = map![
			twox_128(SessionLength::key()).to_vec() => vec![].and(&session_length),
			twox_128(CurrentIndex::key()).to_vec() => vec![].and(&0u64),
			twox_128(Validators::key()).to_vec() => vec![].and(&vec![One.into(), Two.into(), three])
		];
		system::testing::externalities().into_iter().chain(extras.into_iter()).collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::public::*;
	use super::privileged::Dispatch as PrivDispatch;
	use super::internal::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use demo_primitives::AccountId;
	use runtime::session;
	use consensus;

	fn simple_setup() -> TestExternalities {
		map![
			twox_128(SessionLength::key()).to_vec() => vec![].and(&2u64),
			twox_128(CurrentIndex::key()).to_vec() => vec![].and(&0u64),
			// the validators (10, 20, ...)
			twox_128(Validators::key()).to_vec() => vec![].and(&vec![[10u8; 32], [20; 32]]),
			// initial session keys (11, 21, ...)
			b":auth:len".to_vec() => vec![].and(&2u32),
			0u32.to_keyed_vec(b":auth:") => vec![11; 32],
			1u32.to_keyed_vec(b":auth:") => vec![21; 32]
		]
	}

	#[test]
	fn simple_setup_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);
			assert_eq!(length(), 2u64);
			assert_eq!(validators(), vec![[10u8; 32], [20u8; 32]]);
		});
	}

	#[test]
	fn session_length_change_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			// Block 1: Change to length 3; no visible change.
			system::testing::set_block_number(1);
			PrivPass::test().set_length(3);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 0);

			// Block 2: Length now changed to 3. Index incremented.
			system::testing::set_block_number(2);
			PrivPass::test().set_length(3);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 3: Length now changed to 3. Index incremented.
			system::testing::set_block_number(3);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 4: Change to length 2; no visible change.
			system::testing::set_block_number(4);
			PrivPass::test().set_length(2);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 5: Length now changed to 2. Index incremented.
			system::testing::set_block_number(5);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 2);

			// Block 6: No change.
			system::testing::set_block_number(6);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 2);

			// Block 7: Next index.
			system::testing::set_block_number(7);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 3);
		});
	}

	#[test]
	fn session_change_should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			// Block 1: No change
			system::testing::set_block_number(1);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 2: Session rollover, but no change.
			system::testing::set_block_number(2);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 3: Set new key for validator 2; no visible change.
			system::testing::set_block_number(3);
			PublicPass::test(&[20; 32]).set_key([22; 32]);
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 4: Session rollover, authority 2 changes.
			system::testing::set_block_number(4);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [22u8; 32]]);
		});
	}
}
*/
