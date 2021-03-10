#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::Hooks;
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config
	where <Self as frame_system::Config>::AccountId: From<u32>
	{}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where <T as frame_system::Config>::AccountId: From<u32>
	{}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where <T as frame_system::Config>::AccountId: From<u32>
	{}

	#[pallet::type_value] fn Foo<T: Config>() -> u32 { 3u32 }
}

fn main() {
}
