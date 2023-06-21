#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::pallet_macros::*;

pub use pallet::*;

mod first {
	use super::*;

	#[pallet_section]
	mod section {
		#[pallet::event]
		#[pallet::generate_deposit(pub(super) fn deposit_event)]
		pub enum Event<T: Config> {
			SomethingDone,
		}
	}
}

mod second {
	use super::*;
	
	#[pallet_section(section2)]
	mod section {
		#[pallet::error]
		pub enum Error<T> {
			NoneValue,
		}
	}
}

#[import_section(first::section)]
#[import_section(second::section2)]
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

		pub fn my_call_2(_origin: OriginFor<T>) -> DispatchResult {
			return Err(Error::<T>::NoneValue.into())
		}
	}
}

fn main() {
}
