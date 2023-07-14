#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::*;

	#[pallet::config(with_default)]
	pub trait Config: frame_system::Config {
		#[pallet::constant]
		type MyGetParam2: Get<Self::AccountId>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);
}

fn main() {}
