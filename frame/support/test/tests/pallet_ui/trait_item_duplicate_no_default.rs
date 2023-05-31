#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config(with_default)]
	pub trait Config: frame_system::Config {
		#[pallet::constant]
		#[pallet::no_default]
		#[pallet::no_default]
		type MyGetParam2: Get<u32>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

fn main() {}
