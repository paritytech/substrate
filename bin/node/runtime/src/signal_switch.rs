#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::Zero;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			use sp_runtime::generic::DigestItem;
			if ((n + 5u16.into()) % 10u16.into()).is_zero() {
				frame_system::Pallet::<T>::deposit_log(DigestItem::Other(b"switch".to_vec()));
			}
			0
		}
	}

}
