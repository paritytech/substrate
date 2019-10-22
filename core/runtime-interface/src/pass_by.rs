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

//! Provides the [`PassBy`] trait to simplify the implementation of the runtime interface traits
//! for custom types. [`Codec`] and [`Inner`] are the two provided strategy implementations.

use crate::{RIType, impls::{pointer_and_len_from_u64, pointer_and_len_to_u64}};

#[cfg(feature = "std")]
use crate::host::*;
#[cfg(not(feature = "std"))]
use crate::wasm::*;

#[cfg(feature = "std")]
use wasm_interface::{FunctionContext, Pointer, Result};

use rstd::{marker::PhantomData, vec::Vec};

#[cfg(not(feature = "std"))]
use rstd::slice;

pub use substrate_runtime_interface_proc_macro::{PassByCodec, PassByInner};

/// Something that should be passed between wasm and the host using the given strategy.
///
/// See [`Codec`] or [`Inner`] for more information about the provided strategies.
pub trait PassBy: Sized {
	/// The strategy that should be used to pass the type.
	type PassBy: PassByImpl<Self>;
}

/// Something that provides a strategy for passing a type between wasm and the host.
///
/// This trait exposes the same functionality as [`crate::host::IntoFFIValue`] and
/// [`crate::host::FromFFIValue`] to delegate the implementation for a type to a different type.
///
/// This trait is used for the host implementation.
#[cfg(feature = "std")]
pub trait PassByImpl<T>: RIType {
	/// Convert the given instance to the ffi value.
	///
	/// For more information see: [`crate::host::IntoFFIValue::into_ffi_value`]
	fn into_ffi_value(
		instance: T,
		context: &mut dyn FunctionContext,
	) -> Result<Self::FFIType>;

	/// Create `T` from the given ffi value.
	///
	/// For more information see: [`crate::host::FromFFIValue::from_ffi_value`]
	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<T>;
}

/// Something that provides a strategy for passing a type between wasm and the host.
///
/// This trait exposes the same functionality as [`crate::wasm::IntoFFIValue`] and
/// [`crate::wasm::FromFFIValue`] to delegate the implementation for a type to a different type.
///
/// This trait is used for the wasm implementation.
#[cfg(not(feature = "std"))]
pub trait PassByImpl<T>: RIType {
	/// The owned rust type that is stored with the ffi value in [`crate::wasm::WrappedFFIValue`].
	type Owned;

	/// Convert the given `instance` into [`crate::wasm::WrappedFFIValue`].
	///
	/// For more information see: [`crate::wasm::IntoFFIValue::into_ffi_value`]
	fn into_ffi_value(instance: &T) -> WrappedFFIValue<Self::FFIType, Self::Owned>;

	/// Create `T` from the given ffi value.
	///
	/// For more information see: [`crate::wasm::FromFFIValue::from_ffi_value`]
	fn from_ffi_value(arg: Self::FFIType) -> T;
}

/// The implementation of the pass by codec strategy. This strategy uses a SCALE encoded
/// representation of the type between wasm and the host.
///
/// Use this type as associated type for [`PassBy`] to implement this strategy for a type.
///
/// This type expects the type that wants to implement this strategy as generic parameter.
///
/// # Example
/// ```
/// # use substrate_runtime_interface::pass_by::{PassBy, Codec};
/// #[derive(codec::Encode, codec::Decode)]
/// struct Test;
///
/// impl PassBy for Test {
///     type PassBy = Codec<Self>;
/// }
/// ```
pub struct Codec<T: codec::Codec>(PhantomData<T>);

#[cfg(feature = "std")]
impl<T: codec::Codec> PassByImpl<T> for Codec<T> {
	fn into_ffi_value(
		instance: T,
		context: &mut dyn FunctionContext,
	) -> Result<Self::FFIType> {
		let vec = instance.encode();
		let ptr = context.allocate_memory(vec.len() as u32)?;
		context.write_memory(ptr, &vec)?;

		Ok(pointer_and_len_to_u64(ptr.into(), vec.len() as u32))
	}

	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<T> {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let vec = context.read_memory(Pointer::new(ptr), len)?;
		Ok(T::decode(&mut &vec[..]).expect("Wasm to host values are encoded correctly; qed"))
	}
}

#[cfg(not(feature = "std"))]
impl<T: codec::Codec> PassByImpl<T> for Codec<T> {
	type Owned = Vec<u8>;

	fn into_ffi_value(instance: &T) -> WrappedFFIValue<Self::FFIType, Self::Owned> {
		let data = instance.encode();
		let ffi_value = pointer_and_len_to_u64(data.as_ptr() as u32, data.len() as u32);
		(ffi_value, data).into()
	}

	fn from_ffi_value(arg: Self::FFIType) -> T {
		let (ptr, len) = pointer_and_len_from_u64(arg);
		let len = len as usize;

		let slice = unsafe { slice::from_raw_parts(ptr as *const u8, len) };
		T::decode(&mut &slice[..]).expect("Host to wasm values are encoded correctly; qed")
	}
}

impl<T: codec::Codec> RIType for Codec<T> {
	type FFIType = u64;
}

/// Trait that needs to be implemented by a type that should be passed between wasm and the host,
/// by using the inner type. See [`Inner`] for more information.
pub trait PassByInner: Sized {
	/// The inner type that is wrapped by `Self`.
	type Inner: RIType;

	/// Consumes `self` and returns the inner type.
	fn into_inner(self) -> Self::Inner;

	/// Returns the reference to the inner type.
	fn inner(&self) -> &Self::Inner;

	/// Construct `Self` from the given `inner`.
	fn from_inner(inner: Self::Inner) -> Self;
}

/// The implementation of the pass by inner type strategy. The type that uses this strategy will be
/// passed between wasm and the host by using the wrapped inner type. So, this strategy is only
/// usable by newtype structs.
///
/// Use this type as associated type for [`PassBy`] to implement this strategy for a type. Besides
/// that the `PassByInner` trait need to be implemented as well.
///
/// This type expects the type that wants to use this strategy as generic parameter `T` and the
/// inner type as generic parameter `I`.
///
/// # Example
/// ```
/// # use substrate_runtime_interface::pass_by::{PassBy, Inner, PassByInner};
/// struct Test([u8; 32]);
///
/// impl PassBy for Test {
///     type PassBy = Inner<Self, [u8; 32]>;
/// }
///
/// impl PassByInner for Test {
///     type Inner = [u8; 32];
///
///     fn into_inner(self) -> [u8; 32] {
///         self.0
///     }
///     fn inner(&self) -> &[u8; 32] {
///         &self.0
///     }
///     fn from_inner(inner: [u8; 32]) -> Self {
///         Self(inner)
///     }
/// }
/// ```
pub struct Inner<T: PassByInner<Inner = I>, I: RIType>(PhantomData<(T, I)>);

#[cfg(feature = "std")]
impl<T: PassByInner<Inner = I>, I: RIType> PassByImpl<T> for Inner<T, I>
	where I: IntoFFIValue + FromFFIValue<SelfInstance=I>
{
	fn into_ffi_value(
		instance: T,
		context: &mut dyn FunctionContext,
	) -> Result<Self::FFIType> {
		instance.into_inner().into_ffi_value(context)
	}

	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<T> {
		I::from_ffi_value(context, arg).map(T::from_inner)
	}
}

#[cfg(not(feature = "std"))]
impl<T: PassByInner<Inner = I>, I: RIType> PassByImpl<T> for Inner<T, I>
	where I: IntoFFIValue + FromFFIValue
{
	type Owned = I::Owned;

	fn into_ffi_value(instance: &T) -> WrappedFFIValue<Self::FFIType, Self::Owned> {
 		instance.inner().into_ffi_value()
	}

	fn from_ffi_value(arg: Self::FFIType) -> T {
 		T::from_inner(I::from_ffi_value(arg))
	}
}

impl<T: PassByInner<Inner = I>, I: RIType> RIType for Inner<T, I> {
	type FFIType = I::FFIType;
}

impl<T: PassBy> RIType for T {
	type FFIType = <T::PassBy as RIType>::FFIType;
}

#[cfg(feature = "std")]
impl<T: PassBy> IntoFFIValue for T {
	fn into_ffi_value(
		self,
		context: &mut dyn FunctionContext,
	) -> Result<<T::PassBy as RIType>::FFIType> {
		T::PassBy::into_ffi_value(self, context)
	}
}

#[cfg(feature = "std")]
impl<T: PassBy> FromFFIValue for T {
	type SelfInstance = Self;

	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: <T::PassBy as RIType>::FFIType,
	) -> Result<Self> {
		T::PassBy::from_ffi_value(context, arg)
	}
}

#[cfg(not(feature = "std"))]
impl<T: PassBy> IntoFFIValue for T {
	type Owned = <T::PassBy as PassByImpl<T>>::Owned;

	fn into_ffi_value(&self) -> WrappedFFIValue<<T::PassBy as RIType>::FFIType, Self::Owned> {
		T::PassBy::into_ffi_value(self)
	}
}

#[cfg(not(feature = "std"))]
impl<T: PassBy> FromFFIValue for T {
	fn from_ffi_value(arg: <T::PassBy as RIType>::FFIType) -> Self {
		T::PassBy::from_ffi_value(arg)
	}
}

