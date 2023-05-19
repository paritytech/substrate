#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	// Your Pallet's configuration trait, representing custom external types and interfaces.
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::storage]
	type MyStorage<T: Config> = StorageValue<_, Vec<u8>>;

	#[pallet::storage]
	type MyStorageMap<T: Config> = StorageMap<Key = u32, Value = u64>;

	#[pallet::storage]
	type MyStorageDoubleMap<T: Config> = StorageDoubleMap<Key1 = u32, Key2 = u64, Value = u64>;

	#[pallet::storage]
	type MyCountedStorageMap<T: Config> = CountedStorageMap<Key = u32, Value = u64>;

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {}
}

fn main() {}
