#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::{Hooks, DispatchResultWithPostInfo};
	use frame_system::pallet_prelude::{BlockNumberFor, OriginFor};

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}

	struct NotWeight;
	struct WeightInfo;
	impl WeightInfo {
		fn foo() -> NotWeight {
			unimplemented!();
		}
	}
	#[pallet::call]
	#[pallet::weight_info(WeightInfo)]
	impl<T: Config> Pallet<T> {
		fn foo(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			unimplemented!();
		}
	}
}

fn main() {
}
