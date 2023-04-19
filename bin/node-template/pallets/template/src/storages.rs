use frame_support::pallet_macros::*;

#[export_section]
mod storages {

    #[pallet::storage]
	#[pallet::getter(fn something2)]
	pub type Something2<T> = StorageValue<_, u32>;
}