#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::error]
	pub enum Error<T> {}

	#[pallet::storage]
	#[pallet::pov_estimate = MaxEncodedLen]
	#[pallet::pov_estimate = MaxEncodedLen]
	type Foo<T: Config> = StorageValue<_, u8>;
}

fn main() {
}
