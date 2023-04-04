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
		#[pallet::call_index(0)]
        #[pallet::weight(123_u64)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult { Ok(()) }
	}
}

fn main() {
}
