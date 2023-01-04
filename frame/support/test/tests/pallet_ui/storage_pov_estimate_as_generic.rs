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
	type Foo<T: Config> = StorageValue<Value = u8, ProofSize = frame_support::storage::MeasuredProofSize>;
}

fn main() {
}
