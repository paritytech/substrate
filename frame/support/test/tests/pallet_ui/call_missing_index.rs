#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::DispatchResult;
	use frame_system::pallet_prelude::OriginFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn bar(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

fn main() {
}
