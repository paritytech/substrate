#[frame_support::pallet]
mod pallet {
	use codec::{Decode, Encode};
	use frame_support::pallet_prelude::{DispatchResultWithPostInfo, Hooks};
	use frame_system::pallet_prelude::{BlockNumberFor, OriginFor};

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	#[derive(Encode, Decode, scale_info::TypeInfo, PartialEq, Clone)]
	struct Bar;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		#[pallet::call_index(0)]
		pub fn foo(origin: OriginFor<T>, _bar: Bar) -> DispatchResultWithPostInfo {
			Ok(().into())
		}
	}
}

fn main() {}
