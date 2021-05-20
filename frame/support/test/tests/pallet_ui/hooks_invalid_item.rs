#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::Hooks;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);
}

fn main() {
}
