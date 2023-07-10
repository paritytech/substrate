#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config;

	#[pallet::error]
	pub enum Error<T> {
		InvalidCommand,
		XcmVersionNotSupported,
		PreparationMissing,
		ExecutionFailed,
		SendFailed,
		CannotWeigh,
	}

	impl<T: Config> Pallet<T> {}
}
