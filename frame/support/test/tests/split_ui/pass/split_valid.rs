#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::pallet_macros::*;

pub use pallet::*;

#[pallet_section]
mod events {
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		SomethingDone,
	}
}

#[import_section(events)]
#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn my_call(_origin: OriginFor<T>) -> DispatchResult {
			Self::deposit_event(Event::SomethingDone);
			Ok(())
		}
	}
}

fn main() {
}
