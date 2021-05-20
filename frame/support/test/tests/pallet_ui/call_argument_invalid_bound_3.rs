#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, DispatchResultWithPostInfo};
	use frame_system::pallet_prelude::{BlockNumberFor, OriginFor};
	use codec::{Encode, Decode};

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[derive(Encode, Decode)]
	struct Bar;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		fn foo(origin: OriginFor<T>, bar: Bar) -> DispatchResultWithPostInfo {
			Ok(().into())
		}
	}
}

fn main() {
}
