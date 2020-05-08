// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! A pallet that contains common runtime patterns in an isolated manner.
//! This pallet is **not** meant to be used in a production blockchain, just
//! for benchmarking and testing purposes.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{decl_module, decl_storage, decl_event, decl_error};
use frame_support::traits::Currency;
use frame_system::{self as system, ensure_signed};
use codec::{Encode, Decode};
use sp_std::prelude::Vec;

mod benchmarking;

/// Type alias for currency balance.
pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
	type Currency: Currency<Self::AccountId>;
}

// This pallet's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as Benchmark {
		MyMemberList: Vec<T::AccountId>;
		MyMemberMap: map hasher(blake2_128_concat) T::AccountId => bool;
		MyValue: u32;
		MyMap: map hasher(twox_64_concat) u32 => u32;
		MyDoubleMap: double_map hasher(twox_64_concat) u32, hasher(identity) u32 => u32;
	}
}

// The pallet's events
decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		Dummy(u32, AccountId),
	}
);

// The pallet's errors
decl_error! {
	pub enum Error for Module<T: Trait> {
	}
}

// The pallet's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Do nothing.
		#[weight = 0]
		pub fn do_nothing(_origin, input: u32) {
			if input > 0 {
				return Ok(());
			}
		}

		/// Read a value from storage value `repeat` number of times.
		/// Note the first `get()` read here will pull from the underlying
		/// storage database, however, the `repeat` calls will all pull from the
		/// storage overlay cache. You must consider this when analyzing the
		/// results of the benchmark.
		#[weight = 0]
		pub fn read_value(_origin, repeat: u32) {
			for _ in 0..repeat {
				MyValue::get();
			}
		}

		/// Put a value into a storage value.
		#[weight = 0]
		pub fn put_value(_origin, repeat: u32) {
			for r in 0..repeat {
				MyValue::put(r);
			}
		}

		/// Read a value from storage `repeat` number of times.
		/// Note the first `exists()` read here will pull from the underlying
		/// storage database, however, the `repeat` calls will all pull from the
		/// storage overlay cache. You must consider this when analyzing the
		/// results of the benchmark.
		#[weight = 0]
		pub fn exists_value(_origin, repeat: u32) {
			for _ in 0..repeat {
				MyValue::exists();
			}
		}

		/// Remove a value from storage `repeat` number of times.
		#[weight = 0]
		pub fn remove_value(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::remove(r);
			}
		}

		/// Read a value from storage map `repeat` number of times.
		#[weight = 0]
		pub fn read_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::get(r);
			}
		}

		/// Insert a value into a map.
		#[weight = 0]
		pub fn insert_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::insert(r, r);
			}
		}

		/// Check is a map contains a value `repeat` number of times.
		#[weight = 0]
		pub fn contains_key_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::contains_key(r);
			}
		}

		/// Read a value from storage `repeat` number of times.
		#[weight = 0]
		pub fn remove_prefix(_origin, repeat: u32) {
			for r in 0..repeat {
				MyDoubleMap::remove_prefix(r);
			}
		}

		/// Add user to the list.
		#[weight = 0]
		pub fn add_member_list(origin) {
			let who = ensure_signed(origin)?;
			MyMemberList::<T>::mutate(|x| x.push(who));
		}

		/// Append user to the list.
		#[weight = 0]
		pub fn append_member_list(origin) {
			let who = ensure_signed(origin)?;
			MyMemberList::<T>::append(who);
		}

		/// Encode a vector of accounts to bytes.
		#[weight = 0]
		pub fn encode_accounts(_origin, accounts: Vec<T::AccountId>) {
			let bytes = accounts.encode();

			// In an attempt to tell the compiler not to optimize away this benchmark, we will use
			// the result of encoding the accounts.
			if bytes.is_empty() {
				frame_support::print("You are encoding zero accounts.");
			}
		}

		/// Decode bytes into a vector of accounts.
		#[weight = 0]
		pub fn decode_accounts(_origin, bytes: Vec<u8>) {
			let accounts: Vec<T::AccountId> = Decode::decode(&mut bytes.as_slice()).map_err(|_| "Could not decode")?;

			// In an attempt to tell the compiler not to optimize away this benchmark, we will use
			// the result of decoding the bytes.
			if accounts.is_empty() {
				frame_support::print("You are decoding zero bytes.");
			}
		}
	}
}
