#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::error]
	pub enum Error<T> {
		NonExistentValue,
	}

	#[pallet::storage]
	type Foo<T: Config> = StorageValue<_, u8, ResultQuery(NonExistentValue)>;
}

fn main() {
}
