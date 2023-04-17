use macro_magic::*;
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

#[export_tokens]
#[dummy_section]
mod section {
    #[pallet::storage]
	#[pallet::getter(fn something)]
	pub type Something<T> = StorageValue<_, u32>;

    #[pallet::storage]
	#[pallet::getter(fn something2)]
	pub type Something2<T> = StorageValue<_, u32>;

	pub fn t1() {}
}