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

#[cfg(feature = "std")]
extern crate serde;

#[cfg(any(feature = "std", test))]
extern crate substrate_keyring as keyring;

#[cfg(any(feature = "std", test))]
extern crate substrate_primitives;

#[cfg_attr(feature = "std", macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
use primitives::traits::{Zero, One, RefInto, Executable, Convert};
use runtime_support::{StorageValue, StorageMap};

pub trait Trait: consensus::Trait + system::Trait {
	type PublicAux: RefInto<Self::AccountId>;
	type ConvertAccountIdToSessionKey: Convert<Self::AccountId, Self::SessionKey>;
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
		<NextKeyFor<T>>::insert(aux.ref_into(), key)
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
			&new.iter().cloned().map(T::ConvertAccountIdToSessionKey::convert).collect::<Vec<_>>()
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

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait> {
	pub session_length: T::BlockNumber,
	pub validators: Vec<T::AccountId>,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> GenesisConfig<T> where T::AccountId: From<keyring::Keyring> {
	pub fn simple() -> Self where T::AccountId: From<[u8; 32]> {
		use primitives::traits::As;
		use keyring::Keyring::*;
		let three = [3u8; 32];
		GenesisConfig {
			session_length: T::BlockNumber::sa(2),
			validators: vec![T::AccountId::from(One), T::AccountId::from(Two), T::AccountId::from(three)],
		}
	}

	pub fn extended() -> Self {
		use primitives::traits::As;
		use keyring::Keyring::*;
		GenesisConfig {
			session_length: T::BlockNumber::sa(1),
			validators: vec![T::AccountId::from(Alice), T::AccountId::from(Bob), T::AccountId::from(Charlie)],
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		use primitives::traits::As;
		GenesisConfig {
			session_length: T::BlockNumber::sa(1000),
			validators: vec![],
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildExternalities for GenesisConfig<T>
{
	fn build_externalities(self) -> runtime_io::TestExternalities {
		use runtime_io::twox_128;
		use codec::Slicable;
		use primitives::traits::As;
		map![
			twox_128(<SessionLength<T>>::key()).to_vec() => self.session_length.encode(),
			twox_128(<CurrentIndex<T>>::key()).to_vec() => T::BlockNumber::sa(0).encode(),
			twox_128(<Validators<T>>::key()).to_vec() => self.validators.encode()
		]
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use primitives::BuildExternalities;
	use primitives::traits::{HasPublicAux, Identity};
	use primitives::testing::{Digest, Header};

	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl consensus::Trait for Test {
		type SessionKey = u64;
	}
	impl system::Trait for Test {
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = runtime_io::BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
	}
	impl Trait for Test {
		type PublicAux = <Self as HasPublicAux>::PublicAux;
		type ConvertAccountIdToSessionKey = Identity;
	}

	type System = system::Module<Test>;
	type Consensus = consensus::Module<Test>;
	type Session = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::<Test>::default().build_externalities();
		t.extend(consensus::GenesisConfig::<Test>{
			authorities: vec![1, 2, 3],
		}.build_externalities());
		t.extend(GenesisConfig::<Test>{
			session_length: 2,
			validators: vec![1, 2, 3],
		}.build_externalities());
		t
	}

	#[test]
	fn simple_setup_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Consensus::authorities(), vec![1, 2, 3]);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::validators(), vec![1, 2, 3]);
		});
	}

	#[test]
	fn session_length_change_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// Block 1: Change to length 3; no visible change.
			System::set_block_number(1);
			Session::set_length(3);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 0);

			// Block 2: Length now changed to 3. Index incremented.
			System::set_block_number(2);
			Session::set_length(3);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 3: Length now changed to 3. Index incremented.
			System::set_block_number(3);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 4: Change to length 2; no visible change.
			System::set_block_number(4);
			Session::set_length(2);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 5: Length now changed to 2. Index incremented.
			System::set_block_number(5);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 2);

			// Block 6: No change.
			System::set_block_number(6);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 2);

			// Block 7: Next index.
			System::set_block_number(7);
			Session::check_rotate_session();
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 3);
		});
	}

	#[test]
	fn session_change_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// Block 1: No change
			System::set_block_number(1);
			Session::check_rotate_session();
			assert_eq!(Consensus::authorities(), vec![1, 2, 3]);

			// Block 2: Session rollover, but no change.
			System::set_block_number(2);
			Session::check_rotate_session();
			assert_eq!(Consensus::authorities(), vec![1, 2, 3]);

			// Block 3: Set new key for validator 2; no visible change.
			System::set_block_number(3);
			Session::set_key(&2, 5);
			assert_eq!(Consensus::authorities(), vec![1, 2, 3]);

			Session::check_rotate_session();
			assert_eq!(Consensus::authorities(), vec![1, 2, 3]);

			// Block 4: Session rollover, authority 2 changes.
			System::set_block_number(4);
			Session::check_rotate_session();
			assert_eq!(Consensus::authorities(), vec![1, 5, 3]);
		});
	}
}
