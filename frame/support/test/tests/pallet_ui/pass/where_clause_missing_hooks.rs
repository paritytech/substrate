#[frame_support::pallet]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config where <Self as frame_system::Config>::Index: From<u128> {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> where <T as frame_system::Config>::Index: From<u128> {}

	impl<T: Config> Pallet<T> where <T as frame_system::Config>::Index: From<u128> {
		fn foo(x: u128) {
			let _index = <T as frame_system::Config>::Index::from(x);
		}
	}
}

fn main() {}
