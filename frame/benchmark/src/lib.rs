#![cfg_attr(not(feature = "std"), no_std)]

/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/frame/example/src/lib.rs

use frame_support::{decl_module, decl_storage, decl_event, decl_error};
use frame_support::traits::Currency;
use frame_system::{self as system, ensure_signed};
use sp_std::prelude::Vec;

pub mod benchmarking;

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
		MyMemberMap: map hasher(blake2_256) T::AccountId => bool;
		MyValue: u32;
		MyMap: map hasher(blake2_256) u32 => u32;
		MyDoubleMap: double_map hasher(blake2_256) u32, hasher(blake2_256) u32 => u32;
		MyHashMap: map hasher(blake2_256) u128 => u32;
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
		/// Value was None
		NoneValue,
		/// Value reached maximum and cannot be incremented further
		StorageOverflow,
	}
}

// The pallet's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// Initializing errors
		// this includes information about your errors in the node's metadata.
		// it is needed only if you are using errors in your pallet
		type Error = Error<T>;

		// Initializing events
		// this is needed only if you are using events in your pallet
		fn deposit_event() = default;

		/// Do nothing.
		pub fn do_nothing(_origin, input: u32) {
			if input > 0 {
				return Ok(());
			}
		}

		/// Read a value from storage value `repeat` number of times.
		pub fn read_value(_origin, repeat: u32) {
			for _ in 0..repeat {
				MyValue::get();
			}
		}

		/// Put a value into a storage value.
		pub fn put_value(_origin, repeat: u32) {
			for r in 0..repeat {
				MyValue::put(r);
			}
		}

		/// Read a value from storage `repeat` number of times.
		pub fn exists_value(_origin, repeat: u32) {
			for _ in 0..repeat {
				MyValue::exists();
			}
		}

		/// Remove a value from storage `repeat` number of times.
		pub fn remove_value(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::remove(r);
			}
		}

		/// Read a value from storage map `repeat` number of times.
		pub fn read_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::get(r);
			}
		}

		/// Insert a value into a map.
		pub fn insert_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::insert(r, r);
			}
		}

		/// Insert a value into a map.
		pub fn contains_key_map(_origin, repeat: u32) {
			for r in 0..repeat {
				MyMap::contains_key(r);
			}
		}

		/// Read a value from storage `repeat` number of times.
		pub fn remove_prefix(_origin, repeat: u32) {
			for r in 0..repeat {
				MyDoubleMap::remove_prefix(r);
			}
		}

		/// Read a value from storage map `repeat` number of times.
		pub fn read_hash_map(_origin, keys: Vec<u128>) {
			keys.iter().for_each(|key| {
				MyHashMap::get(key);
			});
		}

		/// Insert a value into a map.
		pub fn contains_key_hash_map(_origin, keys: Vec<u128>) {
			keys.iter().for_each(|key| {
				MyHashMap::contains_key(key);
			});
		}

		// Add user to the list.
		pub fn add_member_list(origin) {
			let who = ensure_signed(origin)?;
			MyMemberList::<T>::mutate(|x| x.push(who));
		}

		// Append user to the list.
		pub fn append_member_list(origin) {
			let who = ensure_signed(origin)?;
			MyMemberList::<T>::append(&[who])?;
		}
	}
}
