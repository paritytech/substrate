#[frame_support::pallet]
// Must receive a string literal pointing to a path
#[pallet_doc(X)]
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
