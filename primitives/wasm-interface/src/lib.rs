// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Types and traits for interfacing between the host and the wasm runtime.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{borrow::Cow, iter::Iterator, marker::PhantomData, mem, result, vec, vec::Vec};

#[cfg(not(all(feature = "std", feature = "wasmtime")))]
#[macro_export]
macro_rules! if_wasmtime_is_enabled {
	($($token:tt)*) => {};
}

#[cfg(all(feature = "std", feature = "wasmtime"))]
#[macro_export]
macro_rules! if_wasmtime_is_enabled {
    ($($token:tt)*) => {
        $($token)*
    }
}

if_wasmtime_is_enabled! {
	// Reexport wasmtime so that its types are accessible from the procedural macro.
	pub use wasmtime;

	// Wasmtime uses anyhow types but doesn't reexport them.
	pub use anyhow;
}

/// Result type used by traits in this crate.
#[cfg(feature = "std")]
pub type Result<T> = result::Result<T, String>;
#[cfg(not(feature = "std"))]
pub type Result<T> = result::Result<T, &'static str>;

/// Value types supported by Substrate on the boundary between host/Wasm.
#[derive(Copy, Clone, PartialEq, Debug, Eq)]
pub enum ValueType {
	/// An `i32` value type.
	I32,
	/// An `i64` value type.
	I64,
	/// An `f32` value type.
	F32,
	/// An `f64` value type.
	F64,
}

impl From<ValueType> for u8 {
	fn from(val: ValueType) -> u8 {
		match val {
			ValueType::I32 => 0,
			ValueType::I64 => 1,
			ValueType::F32 => 2,
			ValueType::F64 => 3,
		}
	}
}

impl TryFrom<u8> for ValueType {
	type Error = ();

	fn try_from(val: u8) -> sp_std::result::Result<ValueType, ()> {
		match val {
			0 => Ok(Self::I32),
			1 => Ok(Self::I64),
			2 => Ok(Self::F32),
			3 => Ok(Self::F64),
			_ => Err(()),
		}
	}
}

/// Values supported by Substrate on the boundary between host/Wasm.
#[derive(PartialEq, Debug, Clone, Copy, codec::Encode, codec::Decode)]
pub enum Value {
	/// A 32-bit integer.
	I32(i32),
	/// A 64-bit integer.
	I64(i64),
	/// A 32-bit floating-point number stored as raw bit pattern.
	///
	/// You can materialize this value using `f32::from_bits`.
	F32(u32),
	/// A 64-bit floating-point number stored as raw bit pattern.
	///
	/// You can materialize this value using `f64::from_bits`.
	F64(u64),
}

impl Value {
	/// Returns the type of this value.
	pub fn value_type(&self) -> ValueType {
		match self {
			Value::I32(_) => ValueType::I32,
			Value::I64(_) => ValueType::I64,
			Value::F32(_) => ValueType::F32,
			Value::F64(_) => ValueType::F64,
		}
	}

	/// Return `Self` as `i32`.
	pub fn as_i32(&self) -> Option<i32> {
		match self {
			Self::I32(val) => Some(*val),
			_ => None,
		}
	}
}

/// Provides `Sealed` trait to prevent implementing trait `PointerType` and `WasmTy` outside of this
/// crate.
mod private {
	pub trait Sealed {}

	impl Sealed for u8 {}
	impl Sealed for u16 {}
	impl Sealed for u32 {}
	impl Sealed for u64 {}

	impl Sealed for i32 {}
	impl Sealed for i64 {}
}

/// Something that can be wrapped in a wasm `Pointer`.
///
/// This trait is sealed.
pub trait PointerType: Sized + private::Sealed {
	/// The size of the type in wasm.
	const SIZE: u32 = mem::size_of::<Self>() as u32;
}

impl PointerType for u8 {}
impl PointerType for u16 {}
impl PointerType for u32 {}
impl PointerType for u64 {}

/// Type to represent a pointer in wasm at the host.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Pointer<T: PointerType> {
	ptr: u32,
	_marker: PhantomData<T>,
}

impl<T: PointerType> Pointer<T> {
	/// Create a new instance of `Self`.
	pub fn new(ptr: u32) -> Self {
		Self { ptr, _marker: Default::default() }
	}

	/// Calculate the offset from this pointer.
	///
	/// `offset` is in units of `T`. So, `3` means `3 * mem::size_of::<T>()` as offset to the
	/// pointer.
	///
	/// Returns an `Option` to respect that the pointer could probably overflow.
	pub fn offset(self, offset: u32) -> Option<Self> {
		offset
			.checked_mul(T::SIZE)
			.and_then(|o| self.ptr.checked_add(o))
			.map(|ptr| Self { ptr, _marker: Default::default() })
	}

	/// Create a null pointer.
	pub fn null() -> Self {
		Self::new(0)
	}

	/// Cast this pointer of type `T` to a pointer of type `R`.
	pub fn cast<R: PointerType>(self) -> Pointer<R> {
		Pointer::new(self.ptr)
	}
}

impl<T: PointerType> From<u32> for Pointer<T> {
	fn from(ptr: u32) -> Self {
		Pointer::new(ptr)
	}
}

impl<T: PointerType> From<Pointer<T>> for u32 {
	fn from(ptr: Pointer<T>) -> Self {
		ptr.ptr
	}
}

impl<T: PointerType> From<Pointer<T>> for u64 {
	fn from(ptr: Pointer<T>) -> Self {
		u64::from(ptr.ptr)
	}
}

impl<T: PointerType> From<Pointer<T>> for usize {
	fn from(ptr: Pointer<T>) -> Self {
		ptr.ptr as _
	}
}

impl<T: PointerType> IntoValue for Pointer<T> {
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn into_value(self) -> Value {
		Value::I32(self.ptr as _)
	}
}

impl<T: PointerType> TryFromValue for Pointer<T> {
	fn try_from_value(val: Value) -> Option<Self> {
		match val {
			Value::I32(val) => Some(Self::new(val as _)),
			_ => None,
		}
	}
}

/// The word size used in wasm. Normally known as `usize` in Rust.
pub type WordSize = u32;

/// The Signature of a function
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct Signature {
	/// The arguments of a function.
	pub args: Cow<'static, [ValueType]>,
	/// The optional return value of a function.
	pub return_value: Option<ValueType>,
}

impl Signature {
	/// Create a new instance of `Signature`.
	pub fn new<T: Into<Cow<'static, [ValueType]>>>(
		args: T,
		return_value: Option<ValueType>,
	) -> Self {
		Self { args: args.into(), return_value }
	}

	/// Create a new instance of `Signature` with the given `args` and without any return value.
	pub fn new_with_args<T: Into<Cow<'static, [ValueType]>>>(args: T) -> Self {
		Self { args: args.into(), return_value: None }
	}
}

/// A trait that requires `RefUnwindSafe` when `feature = std`.
#[cfg(feature = "std")]
pub trait MaybeRefUnwindSafe: std::panic::RefUnwindSafe {}
#[cfg(feature = "std")]
impl<T: std::panic::RefUnwindSafe> MaybeRefUnwindSafe for T {}

/// A trait that requires `RefUnwindSafe` when `feature = std`.
#[cfg(not(feature = "std"))]
pub trait MaybeRefUnwindSafe {}
#[cfg(not(feature = "std"))]
impl<T> MaybeRefUnwindSafe for T {}

/// Something that provides a function implementation on the host for a wasm function.
pub trait Function: MaybeRefUnwindSafe + Send + Sync {
	/// Returns the name of this function.
	fn name(&self) -> &str;
	/// Returns the signature of this function.
	fn signature(&self) -> Signature;
	/// Execute this function with the given arguments.
	fn execute(
		&self,
		context: &mut dyn FunctionContext,
		args: &mut dyn Iterator<Item = Value>,
	) -> Result<Option<Value>>;
}

impl PartialEq for dyn Function {
	fn eq(&self, other: &Self) -> bool {
		other.name() == self.name() && other.signature() == self.signature()
	}
}

/// Context used by `Function` to interact with the allocator and the memory of the wasm instance.
pub trait FunctionContext {
	/// Read memory from `address` into a vector.
	fn read_memory(&self, address: Pointer<u8>, size: WordSize) -> Result<Vec<u8>> {
		let mut vec = vec![0; size as usize];
		self.read_memory_into(address, &mut vec)?;
		Ok(vec)
	}
	/// Read memory into the given `dest` buffer from `address`.
	fn read_memory_into(&self, address: Pointer<u8>, dest: &mut [u8]) -> Result<()>;
	/// Write the given data at `address` into the memory.
	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> Result<()>;
	/// Allocate a memory instance of `size` bytes.
	fn allocate_memory(&mut self, size: WordSize) -> Result<Pointer<u8>>;
	/// Deallocate a given memory instance.
	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> Result<()>;
	/// Registers a panic error message within the executor.
	///
	/// This is meant to be used in situations where the runtime
	/// encounters an unrecoverable error and intends to panic.
	///
	/// Panicking in WASM is done through the [`unreachable`](https://webassembly.github.io/spec/core/syntax/instructions.html#syntax-instr-control)
	/// instruction which causes an unconditional trap and immediately aborts
	/// the execution. It does not however allow for any diagnostics to be
	/// passed through to the host, so while we do know that *something* went
	/// wrong we don't have any direct indication of what *exactly* went wrong.
	///
	/// As a workaround we use this method right before the execution is
	/// actually aborted to pass an error message to the host so that it
	/// can associate it with the next trap, and return that to the caller.
	///
	/// A WASM trap should be triggered immediately after calling this method;
	/// otherwise the error message might be associated with a completely
	/// unrelated trap.
	///
	/// It should only be called once, however calling it more than once
	/// is harmless and will overwrite the previously set error message.
	fn register_panic_error_message(&mut self, message: &str);
	fn riscv(&mut self) -> &mut dyn Riscv;
}

pub trait Riscv {
	fn execute(
		&mut self,
		program: &[u8],
		a0: u32,
		syscall_handler: u32,
		state_ptr: u32,
	) -> Result<u8>;

	fn read_memory(&mut self, offset: u32, buf_ptr: u32, buf_len: u32) -> Result<bool>;

	fn write_memory(&mut self, offset: u32, buf_ptr: u32, buf_len: u32) -> Result<bool>;
}

if_wasmtime_is_enabled! {
	/// A trait used to statically register host callbacks with the WASM executor,
	/// so that they call be called from within the runtime with minimal overhead.
	///
	/// This is used internally to interface the wasmtime-based executor with the
	/// host functions' definitions generated through the runtime interface macro,
	/// and is not meant to be used directly.
	pub trait HostFunctionRegistry {
		type State;
		type Error;
		type FunctionContext: FunctionContext;

		/// Wraps the given `caller` in a type which implements `FunctionContext`
		/// and calls the given `callback`.
		fn with_function_context<R>(
			caller: wasmtime::Caller<Self::State>,
			callback: impl FnOnce(&mut dyn FunctionContext) -> R,
		) -> R;

		/// Registers a given host function with the WASM executor.
		///
		/// The function has to be statically callable, and all of its arguments
		/// and its return value have to be compatible with WASM FFI.
		fn register_static<Params, Results>(
			&mut self,
			fn_name: &str,
			func: impl wasmtime::IntoFunc<Self::State, Params, Results> + 'static,
		) -> core::result::Result<(), Self::Error>;
	}
}

/// Something that provides implementations for host functions.
pub trait HostFunctions: 'static + Send + Sync {
	/// Returns the host functions `Self` provides.
	fn host_functions() -> Vec<&'static dyn Function>;

	if_wasmtime_is_enabled! {
		/// Statically registers the host functions.
		fn register_static<T>(registry: &mut T) -> core::result::Result<(), T::Error>
		where
			T: HostFunctionRegistry;
	}
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
impl HostFunctions for Tuple {
	fn host_functions() -> Vec<&'static dyn Function> {
		let mut host_functions = Vec::new();

		for_tuples!( #( host_functions.extend(Tuple::host_functions()); )* );

		host_functions
	}

	#[cfg(all(feature = "std", feature = "wasmtime"))]
	fn register_static<T>(registry: &mut T) -> core::result::Result<(), T::Error>
	where
		T: HostFunctionRegistry,
	{
		for_tuples!(
			#( Tuple::register_static(registry)?; )*
		);

		Ok(())
	}
}

/// A wrapper which merges two sets of host functions, and allows the second set to override
/// the host functions from the first set.
pub struct ExtendedHostFunctions<Base, Overlay> {
	phantom: PhantomData<(Base, Overlay)>,
}

impl<Base, Overlay> HostFunctions for ExtendedHostFunctions<Base, Overlay>
where
	Base: HostFunctions,
	Overlay: HostFunctions,
{
	fn host_functions() -> Vec<&'static dyn Function> {
		let mut base = Base::host_functions();
		let overlay = Overlay::host_functions();
		base.retain(|host_fn| {
			!overlay.iter().any(|ext_host_fn| host_fn.name() == ext_host_fn.name())
		});
		base.extend(overlay);
		base
	}

	if_wasmtime_is_enabled! {
		fn register_static<T>(registry: &mut T) -> core::result::Result<(), T::Error>
		where
			T: HostFunctionRegistry,
		{
			struct Proxy<'a, T> {
				registry: &'a mut T,
				seen_overlay: std::collections::HashSet<String>,
				seen_base: std::collections::HashSet<String>,
				overlay_registered: bool,
			}

			impl<'a, T> HostFunctionRegistry for Proxy<'a, T>
			where
				T: HostFunctionRegistry,
			{
				type State = T::State;
				type Error = T::Error;
				type FunctionContext = T::FunctionContext;

				fn with_function_context<R>(
					caller: wasmtime::Caller<Self::State>,
					callback: impl FnOnce(&mut dyn FunctionContext) -> R,
				) -> R {
					T::with_function_context(caller, callback)
				}

				fn register_static<Params, Results>(
					&mut self,
					fn_name: &str,
					func: impl wasmtime::IntoFunc<Self::State, Params, Results> + 'static,
				) -> core::result::Result<(), Self::Error> {
					if self.overlay_registered {
						if !self.seen_base.insert(fn_name.to_owned()) {
							log::warn!(
								target: "extended_host_functions",
								"Duplicate base host function: '{}'",
								fn_name,
							);

							// TODO: Return an error here?
							return Ok(())
						}

						if self.seen_overlay.contains(fn_name) {
							// Was already registered when we went through the overlay, so just ignore it.
							log::debug!(
								target: "extended_host_functions",
								"Overriding base host function: '{}'",
								fn_name,
							);

							return Ok(())
						}
					} else if !self.seen_overlay.insert(fn_name.to_owned()) {
						log::warn!(
							target: "extended_host_functions",
							"Duplicate overlay host function: '{}'",
							fn_name,
						);

						// TODO: Return an error here?
						return Ok(())
					}

					self.registry.register_static(fn_name, func)
				}
			}

			let mut proxy = Proxy {
				registry,
				seen_overlay: Default::default(),
				seen_base: Default::default(),
				overlay_registered: false,
			};

			// The functions from the `Overlay` can override those from the `Base`,
			// so `Overlay` is registered first, and then we skip those functions
			// in `Base` if they were already registered from the `Overlay`.
			Overlay::register_static(&mut proxy)?;
			proxy.overlay_registered = true;
			Base::register_static(&mut proxy)?;

			Ok(())
		}
	}
}

/// A trait for types directly usable at the WASM FFI boundary without any conversion at all.
///
/// This trait is sealed and should not be implemented downstream.
#[cfg(all(feature = "std", feature = "wasmtime"))]
pub trait WasmTy: wasmtime::WasmTy + private::Sealed {}

/// A trait for types directly usable at the WASM FFI boundary without any conversion at all.
///
/// This trait is sealed and should not be implemented downstream.
#[cfg(not(all(feature = "std", feature = "wasmtime")))]
pub trait WasmTy: private::Sealed {}

impl WasmTy for i32 {}
impl WasmTy for u32 {}
impl WasmTy for i64 {}
impl WasmTy for u64 {}

/// Something that can be converted into a wasm compatible `Value`.
pub trait IntoValue {
	/// The type of the value in wasm.
	const VALUE_TYPE: ValueType;

	/// Convert `self` into a wasm `Value`.
	fn into_value(self) -> Value;
}

/// Something that can may be created from a wasm `Value`.
pub trait TryFromValue: Sized {
	/// Try to convert the given `Value` into `Self`.
	fn try_from_value(val: Value) -> Option<Self>;
}

macro_rules! impl_into_and_from_value {
	(
		$(
			$type:ty, $( < $gen:ident >, )? $value_variant:ident,
		)*
	) => {
		$(
			impl $( <$gen> )? IntoValue for $type {
				const VALUE_TYPE: ValueType = ValueType::$value_variant;
				fn into_value(self) -> Value { Value::$value_variant(self as _) }
			}

			impl $( <$gen> )? TryFromValue for $type {
				fn try_from_value(val: Value) -> Option<Self> {
					match val {
						Value::$value_variant(val) => Some(val as _),
						_ => None,
					}
				}
			}
		)*
	}
}

impl_into_and_from_value! {
	u8, I32,
	u16, I32,
	u32, I32,
	u64, I64,
	i8, I32,
	i16, I32,
	i32, I32,
	i64, I64,
}

/// Typed value that can be returned from a function.
///
/// Basically a `TypedValue` plus `Unit`, for functions which return nothing.
#[derive(Clone, Copy, PartialEq, codec::Encode, codec::Decode, Debug)]
pub enum ReturnValue {
	/// For returning nothing.
	Unit,
	/// For returning some concrete value.
	Value(Value),
}

impl From<Value> for ReturnValue {
	fn from(v: Value) -> ReturnValue {
		ReturnValue::Value(v)
	}
}

impl ReturnValue {
	/// Maximum number of bytes `ReturnValue` might occupy when serialized with `SCALE`.
	///
	/// Breakdown:
	///  1 byte for encoding unit/value variant
	///  1 byte for encoding value type
	///  8 bytes for encoding the biggest value types available in wasm: f64, i64.
	pub const ENCODED_MAX_SIZE: usize = 10;
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Encode;

	#[test]
	fn pointer_offset_works() {
		let ptr = Pointer::<u32>::null();

		assert_eq!(ptr.offset(10).unwrap(), Pointer::new(40));
		assert_eq!(ptr.offset(32).unwrap(), Pointer::new(128));

		let ptr = Pointer::<u64>::null();

		assert_eq!(ptr.offset(10).unwrap(), Pointer::new(80));
		assert_eq!(ptr.offset(32).unwrap(), Pointer::new(256));
	}

	#[test]
	fn return_value_encoded_max_size() {
		let encoded = ReturnValue::Value(Value::I64(-1)).encode();
		assert_eq!(encoded.len(), ReturnValue::ENCODED_MAX_SIZE);
	}
}
