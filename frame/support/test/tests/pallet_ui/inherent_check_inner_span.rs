#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, ProvideInherent};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T> {}
}

fn main() {
}
