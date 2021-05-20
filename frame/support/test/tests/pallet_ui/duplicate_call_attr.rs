#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::Hooks;
	use frame_system::pallet_prelude::BlockNumberFor;
	use frame_support::pallet_prelude::StorageValue;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::generate_store(trait Store)]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::storage]
	type Foo<T> = StorageValue<_, u8>;
}

fn main() {
}
