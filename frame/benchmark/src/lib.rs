#![cfg_attr(not(feature = "std"), no_std)]

/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/frame/example/src/lib.rs

use frame_support::{decl_module, decl_storage, decl_event, decl_error};
use frame_system::{self as system, ensure_signed};
use sp_std::prelude::Vec;

pub mod benchmarking;

/// The pallet's configuration trait.
pub trait Trait: system::Trait {
	// Add other types and constants required to configure this pallet.

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

// This pallet's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as Benchmark {
		MyList: Vec<T::AccountId>;
		MyMap: map hasher(blake2_256) T::AccountId => bool;
	}
}

// The pallet's events
decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		/// Just a dummy event.
		/// Event `Something` is declared with a parameter of the type `u32` and `AccountId`
		/// To emit this event, we call the deposit funtion, from our runtime funtions
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


		pub fn add_member_list(origin) {
			// Check it was signed and get the signer.
			let who = ensure_signed(origin)?;
			// Push user to the list.
			MyList::<T>::mutate(|x| x.push(who));
		}

		pub fn add_member_list_append(origin) {
			// Check it was signed and get the signer.
			let who = ensure_signed(origin)?;
			// Append user to the list.
			MyList::<T>::append(&[who])?;
		}

		pub fn check_member_list(origin) {
			// Check it was signed and get the signer.
			let who = ensure_signed(origin)?;

			// Add user to the list.
			MyList::<T>::mutate(|x| x.push(who));
		}

	}
}
