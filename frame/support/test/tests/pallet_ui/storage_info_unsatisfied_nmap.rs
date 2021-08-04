#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, StorageNMap, Twox64Concat, NMapKey};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[derive(codec::Encode, codec::Decode)]
	struct Bar;

	#[pallet::storage]
	type Foo<T> = StorageNMap<_, NMapKey<Twox64Concat, Bar>, u32>;
}

fn main() {
}
