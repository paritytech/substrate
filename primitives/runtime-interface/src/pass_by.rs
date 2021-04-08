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

//! Provides the [`PassBy`](PassBy) trait to simplify the implementation of the
//! runtime interface traits for custom types.
//!
//! [`Codec`], [`Inner`] and [`Enum`] are the provided strategy implementations.

use crate::{RIType, util::{unpack_ptr_and_len, pack_ptr_and_len}};

#[cfg(feature = "std")]
use crate::host::*;
#[cfg(not(feature = "std"))]
use crate::wasm::*;

#[cfg(feature = "std")]
use sp_wasm_interface::{FunctionContext, Pointer, Result};

use sp_std::{marker::PhantomData, convert::TryFrom};

#[cfg(not(feature = "std"))]
use sp_std::vec::Vec;

/// Derive macro for implementing [`PassBy`] with the [`Codec`] strategy.
///
/// This requires that the type implements [`Encode`](codec::Encode) and [`Decode`](codec::Decode)
/// from `parity-scale-codec`.
///
/// # Example
///
/// ```
/// # use sp_runtime_interface::pass_by::PassByCodec;
/// # use codec::{Encode, Decode};
/// #[derive(PassByCodec, Encode, Decode)]
/// struct EncodableType {
///     name: Vec<u8>,
///     param: u32,
/// }
/// ```
pub use sp_runtime_interface_proc_macro::PassByCodec;

/// Derive macro for implementing [`PassBy`] with the [`Inner`] strategy.
///
/// Besides implementing [`PassBy`], this derive also implements the helper trait [`PassByInner`].
///
/// The type is required to be a struct with just one field. The field type needs to implement
/// the required traits to pass it between the wasm and the native side. (See the runtime interface
/// crate for more information about these traits.)
///
/// # Example
///
/// ```
/// # use sp_runtime_interface::pass_by::PassByInner;
/// #[derive(PassByInner)]
/// struct Data([u8; 32]);
/// ```
///
/// ```
/// # use sp_runtime_interface::pass_by::PassByInner;
/// #[derive(PassByInner)]
/// struct Data {
///     data: [u8; 32],
/// }
/// ```
pub use sp_runtime_interface_proc_macro::PassByInner;

/// Derive macro for implementing [`PassBy`] with the [`Enum`] strategy.
///
/// Besides implementing [`PassBy`], this derive also implements `TryFrom<u8>` and
/// `From<Self> for u8` for the type.
///
/// The type is required to be an enum with only unit variants and at maximum `256` variants. Also
/// it is required that the type implements `Copy`.
///
/// # Example
///
/// ```
/// # use sp_runtime_interface::pass_by::PassByEnum;
/// #[derive(PassByEnum, Copy, Clone)]
/// enum Data {
///     Okay,
///     NotOkay,
///     // This will not work with the derive.
///     //Why(u32),
/// }
/// ```
pub use sp_runtime_interface_proc_macro::PassByEnum;

/// Something that should be passed between wasm and the host using the given strategy.
///
/// See [`Codec`], [`Inner`] or [`Enum`] for more information about the provided strategies.
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

/// The implementation of the pass by codec strategy. This strategy uses a SCALE encoded
/// representation of the type between wasm and the host.
///
/// Use this type as associated type for [`PassBy`] to implement this strategy for a type.
///
/// This type expects the type that wants to implement this strategy as generic parameter.
///
/// [`PassByCodec`](derive.PassByCodec.html) is a derive macro to implement this strategy.
///
/// # Example
/// ```
/// # use sp_runtime_interface::pass_by::{PassBy, Codec};
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

		Ok(pack_ptr_and_len(ptr.into(), vec.len() as u32))
	}

	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<T> {
		let (ptr, len) = unpack_ptr_and_len(arg);
		let vec = context.read_memory(Pointer::new(ptr), len)?;
		T::decode(&mut &vec[..])
			.map_err(|e| format!("Could not decode value from wasm: {}", e))
	}
}

#[cfg(not(feature = "std"))]
impl<T: codec::Codec> PassByImpl<T> for Codec<T> {
	type Owned = Vec<u8>;

	fn into_ffi_value(instance: &T) -> WrappedFFIValue<Self::FFIType, Self::Owned> {
		let data = instance.encode();
		let ffi_value = pack_ptr_and_len(data.as_ptr() as u32, data.len() as u32);
		(ffi_value, data).into()
	}

	fn from_ffi_value(arg: Self::FFIType) -> T {
		let (ptr, len) = unpack_ptr_and_len(arg);
		let len = len as usize;

		let encoded = if len == 0 {
			Vec::new()
		} else {
			unsafe { Vec::from_raw_parts(ptr as *mut u8, len, len) }
		};

		T::decode(&mut &encoded[..]).expect("Host to wasm values are encoded correctly; qed")
	}
}

/// The type is passed as `u64`.
///
/// The `u64` value is build by `length 32bit << 32 | pointer 32bit`
///
/// `Self` is encoded and the length and the pointer are taken from the encoded vector.
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
/// [`PassByInner`](derive.PassByInner.html) is a derive macro to implement this strategy.
///
/// # Example
/// ```
/// # use sp_runtime_interface::pass_by::{PassBy, Inner, PassByInner};
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

/// The type is passed as the inner type.
impl<T: PassByInner<Inner = I>, I: RIType> RIType for Inner<T, I> {
	type FFIType = I::FFIType;
}

/// The implementation of the pass by enum strategy. This strategy uses an `u8` internally to pass
/// the enum between wasm and the host. So, this strategy only supports enums with unit variants.
///
/// Use this type as associated type for [`PassBy`] to implement this strategy for a type.
///
/// This type expects the type that wants to implement this strategy as generic parameter. Besides
/// that the type needs to implement `TryFrom<u8>` and `From<Self> for u8`.
///
/// [`PassByEnum`](derive.PassByEnum.html) is a derive macro to implement this strategy.
///
/// # Example
/// ```
/// # use sp_runtime_interface::pass_by::{PassBy, Enum};
/// #[derive(Clone, Copy)]
/// enum Test {
///     Test1,
///     Test2,
/// }
///
/// impl From<Test> for u8 {
///     fn from(val: Test) -> u8 {
///         match val {
///             Test::Test1 => 0,
///             Test::Test2 => 1,
///         }
///     }
/// }
///
/// impl std::convert::TryFrom<u8> for Test {
///     type Error = ();
///
///     fn try_from(val: u8) -> Result<Test, ()> {
///         match val {
///             0 => Ok(Test::Test1),
///             1 => Ok(Test::Test2),
///             _ => Err(()),
///         }
///     }
/// }
///
/// impl PassBy for Test {
///     type PassBy = Enum<Self>;
/// }
/// ```
pub struct Enum<T: Copy + Into<u8> + TryFrom<u8>>(PhantomData<T>);

#[cfg(feature = "std")]
impl<T: Copy + Into<u8> + TryFrom<u8>> PassByImpl<T> for Enum<T> {
	fn into_ffi_value(
		instance: T,
		_: &mut dyn FunctionContext,
	) -> Result<Self::FFIType> {
		Ok(instance.into())
	}

	fn from_ffi_value(
		_: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<T> {
		T::try_from(arg).map_err(|_| format!("Invalid enum discriminant: {}", arg))
	}
}

#[cfg(not(feature = "std"))]
impl<T: Copy + Into<u8> + TryFrom<u8, Error = ()>> PassByImpl<T> for Enum<T> {
	type Owned = ();

	fn into_ffi_value(instance: &T) -> WrappedFFIValue<Self::FFIType, Self::Owned> {
		let value: u8 = (*instance).into();
		value.into()
	}

	fn from_ffi_value(arg: Self::FFIType) -> T {
		T::try_from(arg).expect("Host to wasm provides a valid enum discriminant; qed")
	}
}

/// The type is passed as `u8`.
///
/// The value is corresponds to the discriminant of the variant.
impl<T: Copy + Into<u8> + TryFrom<u8>> RIType for Enum<T> {
	type FFIType = u8;
}
