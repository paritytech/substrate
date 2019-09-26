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

//! Traits required by the runtime interface from the host side.

use crate::{RIType, pointer_and_len_from_u64, pointer_and_len_to_u64};

use wasm_interface::{FunctionContext, Pointer, Result};

use rstd::{any::TypeId, borrow::Cow, mem};

use codec::{Encode, Decode};

/// Something that can be converted into a ffi value.
pub trait IntoFFIValue: RIType {
	/// Convert `self` into a ffi value.
	fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<Self::FFIType>;
}

/// Something that can be converted into a preallocated ffi value.
///
/// Every type parameter that should be given as `&mut` into a runtime interface function, needs
/// to implement this trait. After executing the host implementation of the runtime interface
/// function, the value is copied into the preallocated wasm memory.
///
/// This should only be used for types which have a fixed size, like slices. Other types like a vec
/// do not work with this interface, as we can not call into wasm to reallocate memory. So, this
/// trait should be implemented carefully.
pub trait IntoPreallocatedFFIValue: RIType {
	/// As `Self` can be an unsized type, it needs to be represented by a sized type at the host.
	/// This `SelfInstance` is the sized type.
	type SelfInstance;

	/// Convert `self_instance` into the given preallocated ffi value.
	fn into_preallocated_ffi_value(
		self_instance: Self::SelfInstance,
		context: &mut dyn FunctionContext,
		allocated: Self::FFIType,
	) -> Result<()>;
}

/// Something that can be created from a ffi value.
pub trait FromFFIValue: RIType {
	/// As `Self` can be an unsized type, it needs to be represented by a sized type at the host.
	/// This `SelfInstance` is the sized type.
	type SelfInstance;

	/// Create `SelfInstance` from the given
	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<Self::SelfInstance>;
}

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

impl<T: 'static + Decode> FromFFIValue for Vec<T> {
	type SelfInstance = Vec<T>;

	fn from_ffi_value(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		<[T] as FromFFIValue>::from_ffi_value(context, arg)
	}
}

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

