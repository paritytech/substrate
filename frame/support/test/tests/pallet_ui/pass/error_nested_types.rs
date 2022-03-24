use codec::{Decode, Encode};
use frame_support::PalletError;

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

#[derive(Encode, Decode, PalletError, scale_info::TypeInfo)]
pub enum MyError {
    Foo,
    Bar,
    Baz(NestedError),
    Struct(MyStruct),
    Wrapper(Wrapper),
}

#[derive(Encode, Decode, PalletError, scale_info::TypeInfo)]
pub enum NestedError {
    Quux
}

#[derive(Encode, Decode, PalletError, scale_info::TypeInfo)]
pub struct MyStruct {
    field: u8,
}

#[derive(Encode, Decode, PalletError, scale_info::TypeInfo)]
pub struct Wrapper(bool);

fn main() {
}
