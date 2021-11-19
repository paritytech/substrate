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

#[derive(frame_support::CompactPalletError, scale_info::TypeInfo)]
pub enum MyError {
    Foo,
    Bar,
    Baz(NestedError),
    Struct(MyStruct),
    Wrapper(Wrapper),
}

#[derive(frame_support::CompactPalletError, scale_info::TypeInfo)]
pub enum NestedError {
    Quux
}

#[derive(frame_support::CompactPalletError, scale_info::TypeInfo)]
pub struct MyStruct {
    field: u8,
}

#[derive(frame_support::CompactPalletError, scale_info::TypeInfo)]
pub struct Wrapper(Option<bool>);

fn main() {
}
