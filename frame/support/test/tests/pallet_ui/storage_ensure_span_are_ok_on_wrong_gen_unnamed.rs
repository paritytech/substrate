#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, StorageValue};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	struct Bar;

	#[pallet::storage]
	type Foo<T> = StorageValue<_, Bar>;
}

fn main() {
}
