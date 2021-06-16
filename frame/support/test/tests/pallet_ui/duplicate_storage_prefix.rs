#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::StorageValue;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::generate_store(trait Store)]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::storage]
	type Foo<T> = StorageValue<_, u8>;

    #[pallet::storage]
    #[pallet::storage_prefix = "Foo"]
    type NotFoo<T> = StorageValue<_, u16>;
}

fn main() {
}
