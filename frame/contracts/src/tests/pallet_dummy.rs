pub use pallet::*;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use frame_support::{
		dispatch::{Pays, PostDispatchInfo},
		pallet_prelude::DispatchResultWithPostInfo,
		weights::Weight,
	};
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Dummy function that overcharges the predispatch weight, allowing us to test the correct
		/// values of [`ContractResult::gas_consumed`] and [`ContractResult::gas_required`] in
		/// tests.
		#[pallet::call_index(1)]
		#[pallet::weight(Weight::from_parts(10_000_000, 0))]
		pub fn overestimate_pre_charge(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			Ok(PostDispatchInfo {
				actual_weight: Some(Weight::from_parts(100, 0)),
				pays_fee: Pays::Yes,
			})
		}
	}
}
