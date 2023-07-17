#[frame_support::pallet]
// Expected one argument for the doc path.
#[pallet_doc]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::Nonce: From<u128>,
	{
	}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);
}

fn main() {}
