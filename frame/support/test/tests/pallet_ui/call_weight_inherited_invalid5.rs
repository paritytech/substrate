// Stray tokens after good input.

#[frame_support::pallet]
mod parentheses {
	use super::*;
	
	#[pallet::config]
	pub trait Config: frame_system::Config {
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::call(weight(<T as Config>::WeightInfo straycat))]
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

	#[pallet::call(weight = <T as Config>::WeightInfo straycat)]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn foo(_: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

fn main() {
}
