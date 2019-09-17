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

//! Traits and macros for creating interfaces between the runtime and the node.

use rstd::{any::TypeId, borrow::Cow, mem};

use wasm_interface::{FunctionContext, IntoValue, TryFromValue, Pointer, Result};

use codec::{Encode, Decode};

pub trait AsFFIArg {
	/// The owned rust type that converts into `Self::FFIType`.
	type RTOwned: IntoFFIArg<Self::FFIType>;
	/// The borrowed rust type that converts into `Self::FFIType`.
	type RTBorrowed: ?Sized + IntoFFIArg<Self::FFIType>;
	type FFIType;

	fn as_ffi_arg<'a>(&'a self) -> FFIArg<'a, Self::FFIType, Self::RTOwned, Self::RTBorrowed>;
}

pub trait FromFFIArg<T>: Sized {
	fn from_ffi_arg(arg: T) -> Self;
}

pub trait FromWasmFFIArg<T>: Sized {
	/// The `Self` instance returned by `from_wasm_ffi_arg`.
	///
	/// For types that are do not implement `Sized` we can not return `Self`. So, we need to use a
	/// wrapper type that stores `Self`.
	type SelfInstance;

	fn from_wasm_ffi_arg(context: &mut dyn FunctionContext, arg: T) -> Result<Self::SelfInstance>;
}

pub trait IntoFFIArg<T> {
	fn into_ffi_arg(&self) -> T;
}

pub trait IntoWasmFFIArg<T> {
	type SelfInstance;

	fn into_wasm_ffi_arg(self_instance: Self::SelfInstance, context: &mut dyn FunctionContext) -> Result<T>;
}

pub enum FFIArg<'a, T, O, R: ?Sized = O> where O: IntoFFIArg<T>, R: IntoFFIArg<T> {
	Ref(&'a R, std::marker::PhantomData<T>),
	Owned(O),
}

impl<'a, T, O: IntoFFIArg<T>, R: ?Sized + IntoFFIArg<T>> FFIArg<'a, T, O, R> {
	pub fn from_owned(o: O) -> Self {
		Self::Owned(o)
	}

	pub fn from_ref(r: &'a R) -> Self {
		Self::Ref(r, Default::default())
	}

	pub fn into_ffi_arg(&self) -> T {
		match self {
			Self::Ref(data, _) => data.into_ffi_arg(),
			Self::Owned(ref data) => data.into_ffi_arg(),
		}
	}
}

impl AsFFIArg for u32 {
	type RTOwned = u32;
	type RTBorrowed = u32;
	type FFIType = u32;

	fn as_ffi_arg<'a>(&'a self) -> FFIArg<'a, u32, u32> {
		FFIArg::from_owned(*self)
	}
}

impl IntoFFIArg<u32> for u32 {
	fn into_ffi_arg(&self) -> u32 {
		self.to_le()
	}
}

impl FromFFIArg<u32> for u32 {
	fn from_ffi_arg(arg: u32) -> u32 {
		u32::from_le(arg)
	}
}

impl<T: ?Sized + AsRef<[u8]>> IntoFFIArg<u64> for T {
	fn into_ffi_arg(&self) -> u64 {
		let data = self.as_ref();

		let ptr_address = data.as_ptr() as u64;

		((data.len() as u64) | ptr_address << 32).to_le()
	}
}

impl<T: 'static + Encode> AsFFIArg for &[T] {
	type RTOwned = Vec<u8>;
	type RTBorrowed = [u8];
	type FFIType = u64;

	fn as_ffi_arg<'a>(&'a self) -> FFIArg<'a, u64, Vec<u8>, [u8]> {
		if TypeId::of::<T>() == TypeId::of::<u8>() {
			let transmuted = unsafe { mem::transmute::<&[T], &[u8]>(self) };
			FFIArg::from_ref(transmuted)
		} else {
			FFIArg::from_owned(self.encode())
		}
	}
}

impl<T: 'static + Encode> AsFFIArg for Vec<T> {
	type RTOwned = Vec<u8>;
	type RTBorrowed = [u8];
	type FFIType = u64;

	fn as_ffi_arg<'a>(&'a self) -> FFIArg<'a, u64, Vec<u8>, [u8]> {
		if TypeId::of::<T>() == TypeId::of::<u8>() {
			let transmuted = unsafe { mem::transmute::<&[T], &[u8]>(&self[..]) };
			FFIArg::from_ref(transmuted)
		} else {
			FFIArg::from_owned(self.encode())
		}
	}
}

impl<T: 'static + Decode> FromFFIArg<u64> for Vec<T> {
	fn from_ffi_arg(arg: u64) -> Vec<T> {
		let arg = u64::from_le(arg);
		let len: usize = (arg & (!0u32 as u64)) as usize;
		let ptr: usize = (arg >> 32) as usize;

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { std::mem::transmute(Vec::from_raw_parts(ptr as *mut u8, len, len)) }
		} else {
			let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len) };
			Self::decode(&mut &slice[..]).expect("Host to Wasm values are encoded correctly; qed")
		}
	}
}

impl<T: 'static + Encode> IntoWasmFFIArg<u64> for Vec<T> {
	type SelfInstance = Vec<T>;

	fn into_wasm_ffi_arg(self_instance: Vec<T>, context: &mut dyn FunctionContext) -> Result<u64> {
		<&[T] as IntoWasmFFIArg<u64>>::into_wasm_ffi_arg(self_instance, context)
	}
}

impl<T: 'static + Decode> FromWasmFFIArg<u64> for Vec<T> {
	type SelfInstance = Vec<T>;

	fn from_wasm_ffi_arg(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		<&[T] as FromWasmFFIArg<u64>>::from_wasm_ffi_arg(context, arg)
	}
}

impl<T: 'static + Encode> IntoWasmFFIArg<u64> for &[T] {
	type SelfInstance = Vec<T>;

	fn into_wasm_ffi_arg(self_instance: Vec<T>, context: &mut dyn FunctionContext) -> Result<u64> {
		let vec: Cow<'_, [u8]> = if TypeId::of::<T>() == TypeId::of::<u8>() {
			unsafe { Cow::Borrowed(std::mem::transmute(&self_instance[..])) }
		} else {
			Cow::Owned(self_instance.encode())
		};

		let ptr = context.allocate_memory(vec.as_ref().len() as u32)?;
		context.write_memory(ptr, &vec)?;

		Ok((vec.len() as u64) | u64::from(ptr) << 32)
	}
}

impl<T: 'static + Decode> FromWasmFFIArg<u64> for &[T] {
	type SelfInstance = Vec<T>;

	fn from_wasm_ffi_arg(context: &mut dyn FunctionContext, arg: u64) -> Result<Vec<T>> {
		let arg = u64::from_le(arg);
		let len = (arg & (!0u32 as u64)) as u32;
		let ptr = (arg >> 32) as u32;

		let vec = context.read_memory(Pointer::new(ptr), len)?;

		if TypeId::of::<T>() == TypeId::of::<u8>() {
			Ok(unsafe { mem::transmute(vec) })
		} else {
			Ok(Vec::<T>::decode(&mut &vec[..]).expect("Wasm to Host values are encoded correctly; qed"))
		}
	}
}
