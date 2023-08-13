use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

// If, for whatever reason, you dont to not use a `WeightInfo` trait - it will still work.
struct Impl;

impl Impl {
	fn foo() -> Weight {
		Weight::zero()
	}
}

#[frame_support::pallet]
mod parentheses {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call(weight(crate::Impl))]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

#[frame_support::pallet]
mod assign {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call(weight = crate::Impl)]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

fn main() {
}
