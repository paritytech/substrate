#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::pallet_macros::*;

#[pallet_section]
mod storages {
	#[pallet::storage]
	pub type MyStorageMap<T: Config> = StorageMap<_, _, u32, u64>;
}

#[import_section(storages)]
pub mod pallet {
	
}

fn main() {
}
