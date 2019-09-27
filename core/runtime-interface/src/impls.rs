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

//! Provides implementations for the runtime interface traits.

use crate::{RIType, PassByCodec};
#[cfg(feature = "std")]
use crate::host::*;
#[cfg(not(feature = "std"))]
use crate::wasm::*;

#[cfg(not(feature = "std"))]
use static_assertions::assert_eq_size;

#[cfg(feature = "std")]
use wasm_interface::{FunctionContext, Pointer, Result};

use codec::{Encode, Decode};

use rstd::{any::TypeId, mem};

#[cfg(feature = "std")]
use rstd::borrow::Cow;

/// Converts a pointer and length into an `u64`.
fn pointer_and_len_to_u64(ptr: u32, len: u32) -> u64 {
	((len as u64) | u64::from(ptr) << 32).to_le()
}

/// Splits an `u64` into the pointer and length.
fn pointer_and_len_from_u64(val: u64) -> (u32, u32) {
	let val = u64::from_le(val);
	let len = (val & (!0u32 as u64)) as u32;
	let ptr = (val >> 32) as u32;

	(ptr, len)
}

/// Implement the traits for the given primitive traits.
macro_rules! impl_traits_for_primitives {
	(
		$(
			$rty:ty, $fty:ty,
		)*
	) => {
		$(
			impl RIType for $rty {
				type FFIType = $fty;
			}

			#[cfg(not(feature = "std"))]
			impl IntoFFIValue for $rty {
				type Owned = ();

				fn into_ffi_value(&self) -> WrappedFFIValue<$fty> {
					(*self as $fty).to_le().into()
				}
			}

			#[cfg(not(feature = "std"))]
			impl FromFFIValue for $rty {
				fn from_ffi_value(arg: $fty) -> $rty {
					<$fty>::from_le(arg) as $rty
				}
			}

			#[cfg(feature = "std")]
			impl FromFFIValue for $rty {
				type SelfInstance = $rty;

				fn from_ffi_value(_: &mut dyn FunctionContext, arg: $fty) -> Result<$rty> {
					Ok(<$fty>::from_le(arg) as $rty)
				}
			}

			#[cfg(feature = "std")]
			impl IntoFFIValue for $rty {
				fn into_ffi_value(self, _: &mut dyn FunctionContext) -> Result<$fty> {
					Ok((self as $fty).to_le())
				}
			}
		)*
	}
}

impl_traits_for_primitives! {
	u8, u8,
	u16, u16,
	u32, u32,
	u64, u64,
	i8, i8,
	i16, i16,
	i32, i32,
	i64, i64,
}

impl RIType for bool {
	type FFIType = u8;
}

#[cfg(not(feature = "std"))]
impl IntoFFIValue for bool {
	type Owned = ();

	fn into_ffi_value(&self) -> WrappedFFIValue<u8> {
		if *self { 1 } else { 0 }.into()
	}
}

#[cfg(not(feature = "std"))]
impl FromFFIValue for bool {
	fn from_ffi_value(arg: u8) -> bool {
		arg == 1
	}
}

#[cfg(feature = "std")]
impl FromFFIValue for bool {
	type SelfInstance = bool;

	fn from_ffi_value(_: &mut dyn FunctionContext, arg: u8) -> Result<bool> {
		Ok(arg == 1)
	}
}

#[cfg(feature = "std")]
impl IntoFFIValue for bool {
	fn into_ffi_value(self, _: &mut dyn FunctionContext) -> Result<u8> {
		Ok(if self { 1 } else { 0 })
	}
}

#[cfg(feature = "std")]
impl<T: 'static + Encode> IntoFFIValue for Vec<T> {
	fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<u64> {
		let vec: Cow<'_, [u8]> = if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { Cow::Borrowed(std::mem::transmute(&self[..])) }
		} else {
			Cow::Owned(self.encode())
		};

		let ptr = context.allocate_memory(vec.as_ref().len() as u32)?;
		context.write_memory(ptr, &vec)?;

		Ok(pointer_and_len_to_u64(ptr.into(), vec.len() as u32))
	}
}

#[cfg(feature = "std")]
impl<T: 'static + Decode> FromFFIValue for Vec<T> {
	type SelfInstance = Vec<T>;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		<[T] as FromFFIValue>::from_ffi_value(context, arg)
	}
}

#[cfg(feature = "std")]
impl<T: 'static + Decode> FromFFIValue for [T] {
	type SelfInstance = Vec<T>;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		let (ptr, len) = pointer_and_len_from_u64(arg);

		let vec = context.read_memory(Pointer::new(ptr), len)?;

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			Ok(unsafe { mem::transmute(vec) })
		} else {
			Ok(Vec::<T>::decode(&mut &vec[..]).expect("Wasm to host values are encoded correctly; qed"))
		}
	}
}

#[cfg(feature = "std")]
impl IntoPreallocatedFFIValue for [u8] {
	type SelfInstance = Vec<u8>;

	fn into_preallocated_ffi_value(
		self_instance: Self::SelfInstance,
		context: &mut dyn FunctionContext,
		allocated: u64,
	) -> Result<()> {
		let (ptr, len) = pointer_and_len_from_u64(allocated);

		if (len as usize) < self_instance.len() {
			Err(
				format!(
					"Preallocated buffer is not big enough (given {} vs needed {})!",
					len,
					self_instance.len()
				)
			)
		} else {
			context.write_memory(Pointer::new(ptr), &self_instance)
		}
	}
}

#[cfg(feature = "std")]
impl<T: PassByCodec> IntoFFIValue for T {
	fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<u64> {
		let vec = self.encode();
		let ptr = context.allocate_memory(vec.len() as u32)?;
		context.write_memory(ptr, &vec)?;

		Ok(pointer_and_len_to_u64(ptr.into(), vec.len() as u32))
	}
}

#[cfg(feature = "std")]
impl<T: PassByCodec> FromFFIValue for T {
	type SelfInstance = Self;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Self> {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let vec = context.read_memory(Pointer::new(ptr), len)?;
		Ok(Self::decode(&mut &vec[..]).expect("Wasm to host values are encoded correctly; qed"))
	}
}

// Make sure that our assumptions for storing a pointer + its size in `u64` is valid.
#[cfg(not(feature = "std"))]
assert_eq_size!(usize_check; usize, u32);
#[cfg(not(feature = "std"))]
assert_eq_size!(ptr_check; *const u8, u32);

#[cfg(not(feature = "std"))]
impl<T: 'static + Encode> IntoFFIValue for [T] {
	type Owned = Vec<u8>;

	fn into_ffi_value(&self) -> WrappedFFIValue<u64, Vec<u8>> {
		if TypeId::of::<T>() == TypeId::of::<u8>() {
			let slice = unsafe { mem::transmute::<&[T], &[u8]>(self) };
			pointer_and_len_to_u64(slice.as_ptr() as u32, slice.len() as u32).into()
		} else {
			let data = self.encode();
			let ffi_value = pointer_and_len_to_u64(data.as_ptr() as u32, data.len() as u32);
			(ffi_value, data).into()
		}
	}
}

#[cfg(not(feature = "std"))]
impl<T: 'static + Encode> IntoFFIValue for Vec<T> {
	type Owned = Vec<u8>;

	fn into_ffi_value(&self) -> WrappedFFIValue<u64, Vec<u8>> {
		self[..].into_ffi_value()
	}
}

#[cfg(not(feature = "std"))]
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

#[cfg(not(feature = "std"))]
impl<T: PassByCodec> IntoFFIValue for T {
	type Owned = Vec<u8>;

	fn into_ffi_value(&self) -> WrappedFFIValue<u64, Vec<u8>> {
		let data = self.encode();
		let ffi_value = pointer_and_len_to_u64(data.as_ptr() as u32, data.len() as u32);
		(ffi_value, data).into()
	}
}

#[cfg(not(feature = "std"))]
impl<T: PassByCodec> FromFFIValue for T {
	fn from_ffi_value(arg: u64) -> Self {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let len = len as usize;

		let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len) };
		Self::decode(&mut &slice[..]).expect("Host to wasm values are encoded correctly; qed")
	}
}
