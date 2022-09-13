#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, IsType};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Bar;
		type RuntimeEvent: IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[pallet::event]
	pub enum Event<T: Config> {
		B { b: T::Bar },
	}
}

fn main() {
}
