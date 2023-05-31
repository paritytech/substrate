#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::pallet_macros::*;

pub use pallet::*;

mod first {
	use super::*;

	#[pallet_section]
	mod storages {
		#[pallet::storage]
		pub type MyStorageMap<T: Config> = StorageMap<_, _, u32, u64>;
	}
}

mod second {
	use super::*;
	
	#[pallet_section(storages2)]
	mod storages {
		#[pallet::storage]
		pub type MyStorageMap2<T: Config> = StorageMap<_, _, u32, u64>;
	}
}

#[import_section(storages)]
#[import_section(storages2)]
#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn my_call(_origin: OriginFor<T>) -> DispatchResult {
			MyStorageMap::<T>::insert(1, 2);
			MyStorageMap2::<T>::insert(1, 2);
			Ok(())
		}
	}
}

fn main() {
}
