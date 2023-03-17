#[frame_support::pallet]
// Supports only one argument.
#[pallet_doc("A", "B")]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::Index: From<u128>,
	{
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);
}

fn main() {}
