#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, PhantomData};

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

fn main() {
}
