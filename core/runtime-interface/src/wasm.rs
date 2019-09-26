// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Traits required by the runtime interface from the wasm side.

use crate::{RIType, pointer_and_len_to_u64, pointer_and_len_from_u64, PassedAsEncoded};

use rstd::{any::TypeId, mem, marker::PhantomData};

use codec::{Encode, Decode};

use static_assertions::assert_eq_size;

/// Something that can be converted into a [`WrappedFFIValue`].
pub trait AsWrappedFFIValue: RIType {
	/// The owned rust type that converts into `Self::FFIType`.
	type RTOwned;
	/// The borrowed rust type that converts into `Self::FFIType`.
	type RTBorrowed: ?Sized;

	/// Returns `self` as a [`WrappedFFIValue`] that can be converted into `Self::FFIType`.
	fn as_wrapped_ffi_value<'a>(
		&'a self,
	) -> WrappedFFIValue<'a, Self::FFIType, Self::RTOwned, Self::RTBorrowed>;
}

/// Something that can be created from a ffi value.
pub trait FromFFIValue: Sized + RIType {
	/// Create `Self` from the given ffi value.
	fn from_ffi_value(arg: Self::FFIType) -> Self;
}

/// Something that can be converted into a ffi value.
pub trait IntoFFIValue: RIType {
	/// Convert `self` into a ffi value.
	fn into_ffi_value(&self) -> Self::FFIType;
}

/// Represents a wrapped ffi value that either holds a reference or an owned value of a rust type.
///
/// The reference and the owned value need to be convertible into the same ffi value.
pub enum WrappedFFIValue<'a, T, O, R: ?Sized = O> {
	Ref(&'a R, PhantomData<T>),
	Owned(O),
}

impl<'a, T, O, R> WrappedFFIValue<'a, T, O, R>
where
	O: IntoFFIValue<FFIType = T>,
	R: ?Sized + IntoFFIValue<FFIType = T>,
{
	/// Create `Self` from an owned value.
	pub fn from_owned(o: O) -> Self {
		Self::Owned(o)
	}

	/// Create `Self` from a reference value.
	pub fn from_ref(r: &'a R) -> Self {
		Self::Ref(r, Default::default())
	}

	/// Convert into the ffi value.
	pub fn into_ffi_value(&self) -> T {
		match self {
			Self::Ref(data, _) => data.into_ffi_value(),
			Self::Owned(ref data) => data.into_ffi_value(),
		}
	}
}

impl AsWrappedFFIValue for u32 {
	type RTOwned = u32;
	type RTBorrowed = u32;

	fn as_wrapped_ffi_value<'a>(&'a self) -> WrappedFFIValue<'a, u32, u32> {
		WrappedFFIValue::from_owned(*self)
	}
}

impl IntoFFIValue for u32 {
	fn into_ffi_value(&self) -> u32 {
		self.to_le()
	}
}

impl FromFFIValue for u32 {
	fn from_ffi_value(arg: u32) -> u32 {
		u32::from_le(arg)
	}
}

// Make sure that our assumptions for storing a pointer + its size in `u64` is valid.
assert_eq_size!(usize_check; usize, u32);
assert_eq_size!(ptr_check; *const u8, u32);

impl IntoFFIValue for [u8] {
	fn into_ffi_value(&self) -> u64 {
		let data = self.as_ref();
		let ptr_address = data.as_ptr() as u32;

		pointer_and_len_to_u64(ptr_address, data.len() as u32)
	}
}

impl IntoFFIValue for Vec<u8> {
	fn into_ffi_value(&self) -> u64 {
		self[..].into_ffi_value()
	}
}

impl<T: 'static + Encode> AsWrappedFFIValue for [T] {
	type RTOwned = Vec<u8>;
	type RTBorrowed = [u8];

	fn as_wrapped_ffi_value<'a>(&'a self) -> WrappedFFIValue<'a, u64, Vec<u8>, [u8]> {
		if TypeId::of::<T>() == TypeId::of::<u8>() {
			WrappedFFIValue::from_ref(unsafe { mem::transmute::<&[T], &[u8]>(self) })
		} else {
			WrappedFFIValue::from_owned(self.encode())
		}
	}
}

impl<T: 'static + Encode> AsWrappedFFIValue for Vec<T> {
	type RTOwned = Vec<u8>;
	type RTBorrowed = [u8];

	fn as_wrapped_ffi_value<'a>(&'a self) -> WrappedFFIValue<'a, u64, Vec<u8>, [u8]> {
		self[..].as_wrapped_ffi_value()
	}
}

impl<T: 'static + Decode> FromFFIValue for Vec<T> {
	fn from_ffi_value(arg: u64) -> Vec<T> {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let len = len as usize;

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { std::mem::transmute(Vec::from_raw_parts(ptr as *mut u8, len, len)) }
		} else {
			let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len) };
			Self::decode(&mut &slice[..]).expect("Host to wasm values are encoded correctly; qed")
		}
	}
}

impl<T: PassedAsEncoded> AsWrappedFFIValue for T {
	type RTOwned = Vec<u8>;
	type RTBorrowed = [u8];

	fn as_wrapped_ffi_value<'a>(&'a self) -> WrappedFFIValue<'a, u64, Vec<u8>, [u8]> {
		WrappedFFIValue::from_owned(self.encode())
	}
}

impl<T: PassedAsEncoded> FromFFIValue for T {
	fn from_ffi_value(arg: u64) -> Self {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let len = len as usize;

		let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len) };
		Self::decode(&mut &slice[..]).expect("Host to wasm values are encoded correctly; qed")
	}
}
