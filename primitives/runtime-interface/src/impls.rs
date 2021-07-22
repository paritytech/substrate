// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Provides implementations for the runtime interface traits.

#[cfg(feature = "std")]
use crate::host::*;
#[cfg(not(feature = "std"))]
use crate::wasm::*;
use crate::{
	pass_by::{Codec, Enum, Inner, PassBy, PassByInner},
	util::{pack_ptr_and_len, unpack_ptr_and_len},
	Pointer, RIType,
};

#[cfg(all(not(feature = "std"), not(feature = "disable_target_static_assertions")))]
use static_assertions::assert_eq_size;

#[cfg(feature = "std")]
use sp_wasm_interface::{FunctionContext, Result};

use codec::{Decode, Encode};

use sp_std::{any::TypeId, mem, vec::Vec};

#[cfg(feature = "std")]
use sp_std::borrow::Cow;

// Make sure that our assumptions for storing a pointer + its size in `u64` is valid.
#[cfg(all(not(feature = "std"), not(feature = "disable_target_static_assertions")))]
assert_eq_size!(usize, u32);
#[cfg(all(not(feature = "std"), not(feature = "disable_target_static_assertions")))]
assert_eq_size!(*const u8, u32);

/// Implement the traits for the given primitive traits.
macro_rules! impl_traits_for_primitives {
	(
		$(
			$rty:ty, $fty:ty,
		)*
	) => {
		$(
			/// The type is passed directly.
			impl RIType for $rty {
				type FFIType = $fty;
			}

			#[cfg(not(feature = "std"))]
			impl IntoFFIValue for $rty {
				type Owned = ();

				fn into_ffi_value(&self) -> WrappedFFIValue<$fty> {
					(*self as $fty).into()
				}
			}

			#[cfg(not(feature = "std"))]
			impl FromFFIValue for $rty {
				fn from_ffi_value(arg: $fty) -> $rty {
					arg as $rty
				}
			}

			#[cfg(feature = "std")]
			impl FromFFIValue for $rty {
				type SelfInstance = $rty;

				fn from_ffi_value(_: &mut dyn FunctionContext, arg: $fty) -> Result<$rty> {
					Ok(arg as $rty)
				}
			}

			#[cfg(feature = "std")]
			impl IntoFFIValue for $rty {
				fn into_ffi_value(self, _: &mut dyn FunctionContext) -> Result<$fty> {
					Ok(self as $fty)
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

/// `bool` is passed as `u8`.
///
/// - `1`: true
/// - `0`: false
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

/// The type is passed as `u64`.
///
/// The `u64` value is build by `length 32bit << 32 | pointer 32bit`
///
/// If `T == u8` the length and the pointer are taken directly from `Self`.
/// Otherwise `Self` is encoded and the length and the pointer are taken from the encoded vector.
impl<T> RIType for Vec<T> {
	type FFIType = u64;
}

#[cfg(feature = "std")]
impl<T: 'static + Encode> IntoFFIValue for Vec<T> {
	fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<u64> {
		let vec: Cow<'_, [u8]> = if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { Cow::Borrowed(mem::transmute(&self[..])) }
		} else {
			Cow::Owned(self.encode())
		};

		let ptr = context.allocate_memory(vec.as_ref().len() as u32)?;
		context.write_memory(ptr, &vec)?;

		Ok(pack_ptr_and_len(ptr.into(), vec.len() as u32))
	}
}

#[cfg(feature = "std")]
impl<T: 'static + Decode> FromFFIValue for Vec<T> {
	type SelfInstance = Vec<T>;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		<[T] as FromFFIValue>::from_ffi_value(context, arg)
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
		let (ptr, len) = unpack_ptr_and_len(arg);
		let len = len as usize;

		if len == 0 {
			return Vec::new()
		}

		let data = unsafe { Vec::from_raw_parts(ptr as *mut u8, len, len) };

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { mem::transmute(data) }
		} else {
			Self::decode(&mut &data[..]).expect("Host to wasm values are encoded correctly; qed")
		}
	}
}

/// The type is passed as `u64`.
///
/// The `u64` value is build by `length 32bit << 32 | pointer 32bit`
///
/// If `T == u8` the length and the pointer are taken directly from `Self`.
/// Otherwise `Self` is encoded and the length and the pointer are taken from the encoded vector.
impl<T> RIType for [T] {
	type FFIType = u64;
}

#[cfg(feature = "std")]
impl<T: 'static + Decode> FromFFIValue for [T] {
	type SelfInstance = Vec<T>;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		let (ptr, len) = unpack_ptr_and_len(arg);

		let vec = context.read_memory(Pointer::new(ptr), len)?;

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			Ok(unsafe { mem::transmute(vec) })
		} else {
			Ok(Vec::<T>::decode(&mut &vec[..])
				.expect("Wasm to host values are encoded correctly; qed"))
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
		let (ptr, len) = unpack_ptr_and_len(allocated);

		if (len as usize) < self_instance.len() {
			Err(format!(
				"Preallocated buffer is not big enough (given {} vs needed {})!",
				len,
				self_instance.len()
			))
		} else {
			context.write_memory(Pointer::new(ptr), &self_instance)
		}
	}
}

#[cfg(not(feature = "std"))]
impl<T: 'static + Encode> IntoFFIValue for [T] {
	type Owned = Vec<u8>;

	fn into_ffi_value(&self) -> WrappedFFIValue<u64, Vec<u8>> {
		if TypeId::of::<T>() == TypeId::of::<u8>() {
			let slice = unsafe { mem::transmute::<&[T], &[u8]>(self) };
			pack_ptr_and_len(slice.as_ptr() as u32, slice.len() as u32).into()
		} else {
			let data = self.encode();
			let ffi_value = pack_ptr_and_len(data.as_ptr() as u32, data.len() as u32);
			(ffi_value, data).into()
		}
	}
}

/// Implement the traits for the `[u8; N]` arrays, where `N` is the input to this macro.
macro_rules! impl_traits_for_arrays {
	(
		$(
			$n:expr
		),*
		$(,)?
	) => {
		$(
			/// The type is passed as `u32`.
			///
			/// The `u32` is the pointer to the array.
			impl RIType for [u8; $n] {
				type FFIType = u32;
			}

			#[cfg(not(feature = "std"))]
			impl IntoFFIValue for [u8; $n] {
				type Owned = ();

				fn into_ffi_value(&self) -> WrappedFFIValue<u32> {
					(self.as_ptr() as u32).into()
				}
			}

			#[cfg(not(feature = "std"))]
			impl FromFFIValue for [u8; $n] {
				fn from_ffi_value(arg: u32) -> [u8; $n] {
					let mut res = [0u8; $n];
					let data = unsafe { Vec::from_raw_parts(arg as *mut u8, $n, $n) };

					res.copy_from_slice(&data);

					res
				}
			}

			#[cfg(feature = "std")]
			impl FromFFIValue for [u8; $n] {
				type SelfInstance = [u8; $n];

				fn from_ffi_value(context: &mut dyn FunctionContext, arg: u32) -> Result<[u8; $n]> {
					let data = context.read_memory(Pointer::new(arg), $n)?;
					let mut res = [0u8; $n];
					res.copy_from_slice(&data);
					Ok(res)
				}
			}

			#[cfg(feature = "std")]
			impl IntoFFIValue for [u8; $n] {
				fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<u32> {
					let addr = context.allocate_memory($n)?;
					context.write_memory(addr, &self)?;
					Ok(addr.into())
				}
			}

			#[cfg(feature = "std")]
			impl IntoPreallocatedFFIValue for [u8; $n] {
				type SelfInstance = [u8; $n];

				fn into_preallocated_ffi_value(
					self_instance: Self::SelfInstance,
					context: &mut dyn FunctionContext,
					allocated: u32,
				) -> Result<()> {
					context.write_memory(Pointer::new(allocated), &self_instance)
				}
			}
		)*
	}
}

impl_traits_for_arrays! {
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
	27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
	51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
	75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
}

impl<T: codec::Codec, E: codec::Codec> PassBy for sp_std::result::Result<T, E> {
	type PassBy = Codec<Self>;
}

impl<T: codec::Codec> PassBy for Option<T> {
	type PassBy = Codec<Self>;
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
#[tuple_types_no_default_trait_bound]
impl PassBy for Tuple
where
	Self: codec::Codec,
{
	type PassBy = Codec<Self>;
}

/// Implement `PassBy` with `Inner` for the given fixed sized hash types.
macro_rules! for_primitive_types {
	{ $( $hash:ident $n:expr ),* $(,)? } => {
		$(
			impl PassBy for primitive_types::$hash {
				type PassBy = Inner<Self, [u8; $n]>;
			}

			impl PassByInner for primitive_types::$hash {
				type Inner = [u8; $n];

				fn inner(&self) -> &Self::Inner {
					&self.0
				}

				fn into_inner(self) -> Self::Inner {
					self.0
				}

				fn from_inner(inner: Self::Inner) -> Self {
					Self(inner)
				}
			}
		)*
	}
}

for_primitive_types! {
	H160 20,
	H256 32,
	H512 64,
}

/// The type is passed as `u64`.
///
/// The `u64` value is build by `length 32bit << 32 | pointer 32bit`
///
/// The length and the pointer are taken directly from `Self`.
impl RIType for str {
	type FFIType = u64;
}

#[cfg(feature = "std")]
impl FromFFIValue for str {
	type SelfInstance = String;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<String> {
		let (ptr, len) = unpack_ptr_and_len(arg);

		let vec = context.read_memory(Pointer::new(ptr), len)?;

		// The data is valid utf8, as it is stored as `&str` in wasm.
		String::from_utf8(vec).map_err(|_| "Invalid utf8 data provided".into())
	}
}

#[cfg(not(feature = "std"))]
impl IntoFFIValue for str {
	type Owned = ();

	fn into_ffi_value(&self) -> WrappedFFIValue<u64, ()> {
		let bytes = self.as_bytes();
		pack_ptr_and_len(bytes.as_ptr() as u32, bytes.len() as u32).into()
	}
}

#[cfg(feature = "std")]
impl<T: sp_wasm_interface::PointerType> RIType for Pointer<T> {
	type FFIType = u32;
}

/// The type is passed as `u32`.
#[cfg(not(feature = "std"))]
impl<T> RIType for Pointer<T> {
	type FFIType = u32;
}

#[cfg(not(feature = "std"))]
impl<T> IntoFFIValue for Pointer<T> {
	type Owned = ();

	fn into_ffi_value(&self) -> WrappedFFIValue<u32> {
		(*self as u32).into()
	}
}

#[cfg(not(feature = "std"))]
impl<T> FromFFIValue for Pointer<T> {
	fn from_ffi_value(arg: u32) -> Self {
		arg as _
	}
}

#[cfg(feature = "std")]
impl<T: sp_wasm_interface::PointerType> FromFFIValue for Pointer<T> {
	type SelfInstance = Self;

	fn from_ffi_value(_: &mut dyn FunctionContext, arg: u32) -> Result<Self> {
		Ok(Pointer::new(arg))
	}
}

#[cfg(feature = "std")]
impl<T: sp_wasm_interface::PointerType> IntoFFIValue for Pointer<T> {
	fn into_ffi_value(self, _: &mut dyn FunctionContext) -> Result<u32> {
		Ok(self.into())
	}
}

/// Implement the traits for `u128`/`i128`
macro_rules! for_u128_i128 {
	($type:ty) => {
		/// `u128`/`i128` is passed as `u32`.
		///
		/// The `u32` is a pointer to an `[u8; 16]` array.
		impl RIType for $type {
			type FFIType = u32;
		}

		#[cfg(not(feature = "std"))]
		impl IntoFFIValue for $type {
			type Owned = ();

			fn into_ffi_value(&self) -> WrappedFFIValue<u32> {
				unsafe { (mem::transmute::<&Self, *const u8>(self) as u32).into() }
			}
		}

		#[cfg(not(feature = "std"))]
		impl FromFFIValue for $type {
			fn from_ffi_value(arg: u32) -> $type {
				<$type>::from_le_bytes(<[u8; mem::size_of::<$type>()]>::from_ffi_value(arg))
			}
		}

		#[cfg(feature = "std")]
		impl FromFFIValue for $type {
			type SelfInstance = $type;

			fn from_ffi_value(context: &mut dyn FunctionContext, arg: u32) -> Result<$type> {
				let data =
					context.read_memory(Pointer::new(arg), mem::size_of::<$type>() as u32)?;
				let mut res = [0u8; mem::size_of::<$type>()];
				res.copy_from_slice(&data);
				Ok(<$type>::from_le_bytes(res))
			}
		}

		#[cfg(feature = "std")]
		impl IntoFFIValue for $type {
			fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<u32> {
				let addr = context.allocate_memory(mem::size_of::<$type>() as u32)?;
				context.write_memory(addr, &self.to_le_bytes())?;
				Ok(addr.into())
			}
		}
	};
}

for_u128_i128!(u128);
for_u128_i128!(i128);

impl PassBy for sp_wasm_interface::ValueType {
	type PassBy = Enum<sp_wasm_interface::ValueType>;
}

impl PassBy for sp_wasm_interface::Value {
	type PassBy = Codec<sp_wasm_interface::Value>;
}

impl PassBy for sp_storage::TrackedStorageKey {
	type PassBy = Codec<Self>;
}
