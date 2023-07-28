#[frame_support::pallet]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	#[pallet::generate_storage_info] // invalid
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

fn main() {
}
