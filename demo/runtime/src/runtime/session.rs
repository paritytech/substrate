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

use rstd::prelude::*;
use codec::KeyedVec;
use runtime_support::{storage, StorageValue, StorageMap};
use demo_primitives::{AccountId, SessionKey, BlockNumber};
use runtime::{system, staking, consensus};
use runtime::democracy::PrivPass;
use runtime::staking::PublicPass;

storage_items!{
	// The current set of validators.
	pub Validators get(validators): b"ses:val" => required Vec<AccountId>;
	// Current length of the session.
	pub SessionLength get(length): b"ses:len" => required BlockNumber;
	// Current index of the session.
	pub CurrentIndex get(current_index): b"ses:ind" => required BlockNumber;

	// Block at which the session length last changed.
	LastLengthChange: b"ses:llc" => default BlockNumber;
	// The next key for a given validator.
	NextKeyFor: b"ses:nxt:" => map [ AccountId => SessionKey ];
	// The next session length.
	NextSessionLength: b"ses:nln" => BlockNumber;
}

/// The number of validators currently.
pub fn validator_count() -> u32 {
	Validators::get().len() as u32	// TODO: can probably optimised
}

impl_dispatch! {
	pub mod public;
	fn set_key(key: SessionKey) = 0;
}

impl<'a> public::Dispatch for PublicPass<'a> {
	/// Sets the session key of `_validator` to `_key`. This doesn't take effect until the next
	/// session.
	fn set_key(self, key: SessionKey) {
		// set new value for next session
		NextKeyFor::insert(*self, key)
	}
}

impl_dispatch! {
	pub mod privileged;
	fn set_length(new: BlockNumber) = 0;
	fn force_new_session() = 1;
}

impl privileged::Dispatch for PrivPass {
	/// Set a new era length. Won't kick in until the next era change (at current length).
	fn set_length(self, new: BlockNumber) {
		NextSessionLength::put(new);
	}

	/// Forces a new session.
	fn force_new_session(self) {
		internal::rotate_session();
	}
}

// INTERNAL API (available to other runtime modules)

pub mod internal {
	use super::*;

	/// Set the current set of validators.
	///
	/// Called by `staking::next_era()` only. `next_session` should be called after this in order to
	/// update the session keys to the next validator set.
	pub fn set_validators(new: &[AccountId]) {
		Validators::put(&new.to_vec());			// TODO: optimise.
		consensus::internal::set_authorities(new);
	}

	/// Hook to be called after transaction processing.
	pub fn check_rotate_session() {
		// do this last, after the staking system has had chance to switch out the authorities for the
		// new set.
		// check block number and call next_session if necessary.
		if (system::block_number() - LastLengthChange::get()) % length() == 0 {
			rotate_session();
		}
	}

	/// Move onto next session: register the new authority set.
	pub fn rotate_session() {
		// Increment current session index.
		CurrentIndex::put(CurrentIndex::get() + 1);

		// Enact era length change.
		if let Some(next_len) = NextSessionLength::take() {
			SessionLength::put(next_len);
			LastLengthChange::put(system::block_number());
		}

		// Update any changes in session keys.
		validators().iter().enumerate().for_each(|(i, v)| {
			if let Some(n) = NextKeyFor::take(v) {
				consensus::internal::set_authority(i as u32, &n);
			}
		});
	}
}

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
	use environment::with_env;
	use demo_primitives::AccountId;
	use runtime::{consensus, session};

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
			with_env(|e| e.block_number = 1);
			PrivPass::test().set_length(3);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 0);

			// Block 2: Length now changed to 3. Index incremented.
			with_env(|e| e.block_number = 2);
			PrivPass::test().set_length(3);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 3: Length now changed to 3. Index incremented.
			with_env(|e| e.block_number = 3);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 4: Change to length 2; no visible change.
			with_env(|e| e.block_number = 4);
			PrivPass::test().set_length(2);
			check_rotate_session();
			assert_eq!(length(), 3);
			assert_eq!(current_index(), 1);

			// Block 5: Length now changed to 2. Index incremented.
			with_env(|e| e.block_number = 5);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 2);

			// Block 6: No change.
			with_env(|e| e.block_number = 6);
			check_rotate_session();
			assert_eq!(length(), 2);
			assert_eq!(current_index(), 2);

			// Block 7: Next index.
			with_env(|e| e.block_number = 7);
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
			with_env(|e| e.block_number = 1);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 2: Session rollover, but no change.
			with_env(|e| e.block_number = 2);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 3: Set new key for validator 2; no visible change.
			with_env(|e| e.block_number = 3);
			PublicPass::test(&[20; 32]).set_key([22; 32]);
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [21u8; 32]]);

			// Block 4: Session rollover, authority 2 changes.
			with_env(|e| e.block_number = 4);
			check_rotate_session();
			assert_eq!(consensus::authorities(), vec![[11u8; 32], [22u8; 32]]);
		});
	}
}
