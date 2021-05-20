#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, PhantomData};
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::type_value] struct Foo;
}

fn main() {
}
