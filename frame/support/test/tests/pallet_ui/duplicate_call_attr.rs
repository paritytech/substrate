#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{StorageValue, Hooks, Weight};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::generate_store(trait Store)]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>, Weight> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[pallet::storage]
	type Foo<T> = StorageValue<_, u8>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

fn main() {
}
