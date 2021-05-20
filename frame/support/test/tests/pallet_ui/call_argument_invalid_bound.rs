#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, DispatchResultWithPostInfo};
	use frame_system::pallet_prelude::{BlockNumberFor, OriginFor};

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Bar: codec::Codec;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		fn foo(origin: OriginFor<T>, bar: T::Bar) -> DispatchResultWithPostInfo {
			Ok(().into())
		}
	}
}

fn main() {
}
