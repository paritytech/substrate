use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

pub trait WeightInfo {
	fn foo() -> Weight;
}

#[frame_support::pallet(dev_mode)]
mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type WeightInfo: WeightInfo;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call(weight(<T as Config>::WeightInfo))]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

fn main() {
}
