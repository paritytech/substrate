#[frame_support::pallet]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::error]
	pub enum Error<T> {
		CustomError(crate::MyError),
	}
}

#[derive(scale_info::TypeInfo, codec::Encode, codec::Decode)]
enum MyError {}

fn main() {
}
