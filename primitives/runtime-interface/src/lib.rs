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

//! Substrate runtime interface
//!
//! This crate provides types, traits and macros around runtime interfaces. A runtime interface is
//! a fixed interface between a Substrate runtime and a Substrate node. For a native runtime the
//! interface maps to a direct function call of the implementation. For a wasm runtime the interface
//! maps to an external function call. These external functions are exported by the wasm executor
//! and they map to the same implementation as the native calls.
//!
//! # Using a type in a runtime interface
//!
//! Any type that should be used in a runtime interface as argument or return value needs to
//! implement [`RIType`]. The associated type [`FFIType`](./trait.RIType.html#associatedtype.FFIType)
//! is the type that is used in the FFI function to represent the actual type. For example `[T]` is
//! represented by an `u64`. The slice pointer and the length will be mapped to an `u64` value.
//! For more information see this [table](#ffi-type-and-conversion).
//! The FFI function definition is used when calling from the wasm runtime into the node.
//!
//! Traits are used to convert from a type to the corresponding
//! [`RIType::FFIType`](./trait.RIType.html#associatedtype.FFIType).
//! Depending on where and how a type should be used in a function signature, a combination of the
//! following traits need to be implemented:
//! <!-- markdown-link-check-enable -->
//! 1. Pass as function argument: [`wasm::IntoFFIValue`] and [`host::FromFFIValue`]
//! 2. As function return value: [`wasm::FromFFIValue`] and [`host::IntoFFIValue`]
//! 3. Pass as mutable function argument: [`host::IntoPreallocatedFFIValue`]
//!
//! The traits are implemented for most of the common types like `[T]`, `Vec<T>`, arrays and
//! primitive types.
//!
//! For custom types, we provide the [`PassBy`](./pass_by#PassBy) trait and strategies that define
//! how a type is passed between the wasm runtime and the node. Each strategy also provides a derive
//! macro to simplify the implementation.
//!
//! # Performance
//!
//! To not waste any more performance when calling into the node, not all types are SCALE encoded
//! when being passed as arguments between the wasm runtime and the node. For most types that
//! are raw bytes like `Vec<u8>`, `[u8]` or `[u8; N]` we pass them directly, without SCALE encoding
//! them in front of. The implementation of [`RIType`] each type provides more information on how
//! the data is passed.
//!
//! # Declaring a runtime interface
//!
//! Declaring a runtime interface is similar to declaring a trait in Rust:
//!
//! ```
//! #[sp_runtime_interface::runtime_interface]
//! trait RuntimeInterface {
//!     fn some_function(value: &[u8]) -> bool {
//!         value.iter().all(|v| *v > 125)
//!     }
//! }
//! ```
//!
//! For more information on declaring a runtime interface, see
//! [`#[runtime_interface]`](./attr.runtime_interface.html).
//!
//! # FFI type and conversion
//!
//! The following table documents how values of types are passed between the wasm and
//! the host side and how they are converted into the corresponding type.
//!
//! | Type | FFI type | Conversion |
//! |----|----|----|
//! | `u8` | `u8` | `Identity` |
//! | `u16` | `u16` | `Identity` |
//! | `u32` | `u32` | `Identity` |
//! | `u64` | `u64` | `Identity` |
//! | `i128` | `u32` | `v.as_ptr()` (pointer to a 16 byte array) |
//! | `i8` | `i8` | `Identity` |
//! | `i16` | `i16` | `Identity` |
//! | `i32` | `i32` | `Identity` |
//! | `i64` | `i64` | `Identity` |
//! | `u128` | `u32` | `v.as_ptr()` (pointer to a 16 byte array) |
//! | `bool` | `u8` | `if v { 1 } else { 0 }` |
//! | `&str` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
//! | `&[u8]` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
//! | `Vec<u8>` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
//! | `Vec<T> where T: Encode` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
//! | `&[T] where T: Encode` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
//! | `[u8; N]` | `u32` | `v.as_ptr()` |
//! | `*const T` | `u32` | `Identity` |
//! | `Option<T>` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
//! | [`T where T: PassBy<PassBy=Inner>`](./pass_by#Inner) | Depends on inner | Depends on inner |
//! | [`T where T: PassBy<PassBy=Codec>`](./pass_by#Codec)|`u64`|<code>v.len() 32bit << 32 &#124;v.as_ptr() 32bit</code>|
//!
//! `Identity` means that the value is converted directly into the corresponding FFI type.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate self as sp_runtime_interface;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use sp_wasm_interface;

#[doc(hidden)]
pub use sp_tracing;

#[doc(hidden)]
pub use sp_std;

/// Attribute macro for transforming a trait declaration into a runtime interface.
///
/// A runtime interface is a fixed interface between a Substrate compatible runtime and the native
/// node. This interface is callable from a native and a wasm runtime. The macro will generate the
/// corresponding code for the native implementation and the code for calling from the wasm
/// side to the native implementation.
///
/// The macro expects the runtime interface declaration as trait declaration:
///
/// ```
/// # use sp_runtime_interface::runtime_interface;
///
/// #[runtime_interface]
/// trait Interface {
///     /// A function that can be called from native/wasm.
///     ///
///     /// The implementation given to this function is only compiled on native.
///     fn call(data: &[u8]) -> Vec<u8> {
///         // Here you could call some rather complex code that only compiles on native or
///         // is way faster in native than executing it in wasm.
///         Vec::new()
///     }
///     /// Call function, but different version.
///     ///
///     /// For new runtimes, only function with latest version is reachable.
///     /// But old version (above) is still accessible for old runtimes.
///     /// Default version is 1.
///     #[version(2)]
///     fn call(data: &[u8]) -> Vec<u8> {
///         // Here you could call some rather complex code that only compiles on native or
///         // is way faster in native than executing it in wasm.
///         [17].to_vec()
///     }
///
///     /// A function can take a `&self` or `&mut self` argument to get access to the
///     /// `Externalities`. (The generated method does not require
///     /// this argument, so the function can be called just with the `optional` argument)
///     fn set_or_clear(&mut self, optional: Option<Vec<u8>>) {
///         match optional {
///             Some(value) => self.set_storage([1, 2, 3, 4].to_vec(), value),
///             None => self.clear_storage(&[1, 2, 3, 4]),
///         }
///     }
/// }
/// ```
///
///
/// The given example will generate roughly the following code for native:
///
/// ```
/// // The name of the trait is converted to snake case and used as mod name.
/// //
/// // Be aware that this module is not `public`, the visibility of the module is determined based
/// // on the visibility of the trait declaration.
/// mod interface {
///     trait Interface {
///         fn call_version_1(data: &[u8]) -> Vec<u8>;
///         fn call_version_2(data: &[u8]) -> Vec<u8>;
///         fn set_or_clear_version_1(&mut self, optional: Option<Vec<u8>>);
///     }
///
///     impl Interface for &mut dyn sp_externalities::Externalities {
///         fn call_version_1(data: &[u8]) -> Vec<u8> { Vec::new() }
///         fn call_version_2(data: &[u8]) -> Vec<u8> { [17].to_vec() }
///         fn set_or_clear_version_1(&mut self, optional: Option<Vec<u8>>) {
///             match optional {
///                 Some(value) => self.set_storage([1, 2, 3, 4].to_vec(), value),
///                 None => self.clear_storage(&[1, 2, 3, 4]),
///             }
///         }
///     }
///
///     pub fn call(data: &[u8]) -> Vec<u8> {
///         // only latest version is exposed
///         call_version_2(data)
///     }
///
///     fn call_version_1(data: &[u8]) -> Vec<u8> {
///         <&mut dyn sp_externalities::Externalities as Interface>::call_version_1(data)
///     }
///
///     fn call_version_2(data: &[u8]) -> Vec<u8> {
///         <&mut dyn sp_externalities::Externalities as Interface>::call_version_2(data)
///     }
///
///     pub fn set_or_clear(optional: Option<Vec<u8>>) {
///         set_or_clear_version_1(optional)
///     }
///
///     fn set_or_clear_version_1(optional: Option<Vec<u8>>) {
///         sp_externalities::with_externalities(|mut ext| Interface::set_or_clear_version_1(&mut ext, optional))
///             .expect("`set_or_clear` called outside of an Externalities-provided environment.")
///     }
///
///     /// This type implements the `HostFunctions` trait (from `sp-wasm-interface`) and
///     /// provides the host implementation for the wasm side. The host implementation converts the
///     /// arguments from wasm to native and calls the corresponding native function.
///     ///
///     /// This type needs to be passed to the wasm executor, so that the host functions will be
///     /// registered in the executor.
///     pub struct HostFunctions;
/// }
/// ```
///
///
/// The given example will generate roughly the following code for wasm:
///
/// ```
/// mod interface {
///     mod extern_host_functions_impls {
///         extern "C" {
///             /// Every function is exported as `ext_TRAIT_NAME_FUNCTION_NAME_version_VERSION`.
///             ///
///             /// `TRAIT_NAME` is converted into snake case.
///             ///
///             /// The type for each argument of the exported function depends on
///             /// `<ARGUMENT_TYPE as RIType>::FFIType`.
///             ///
///             /// `data` holds the pointer and the length to the `[u8]` slice.
///             pub fn ext_Interface_call_version_1(data: u64) -> u64;
///             /// `optional` holds the pointer and the length of the encoded value.
///             pub fn ext_Interface_set_or_clear_version_1(optional: u64);
///         }
///     }
///
///     /// The type is actually `ExchangeableFunction` (from `sp-runtime-interface`).
///     ///
///     /// This can be used to replace the implementation of the `call` function.
///     /// Instead of calling into the host, the callee will automatically call the other
///     /// implementation.
///     ///
///     /// To replace the implementation:
///     ///
///     /// `host_call.replace_implementation(some_other_impl)`
///     pub static host_call: () = ();
///     pub static host_set_or_clear: () = ();
///
///     pub fn call(data: &[u8]) -> Vec<u8> {
///         // This is the actual call: `host_call.get()(data)`
///         //
///         // But that does not work for several reasons in this example, so we just return an
///         // empty vector.
///         Vec::new()
///     }
///
///     pub fn set_or_clear(optional: Option<Vec<u8>>) {
///         // Same as above
///     }
/// }
/// ```
///
/// # Argument types
///
/// The macro supports any kind of argument type, as long as it implements [`RIType`] and the
/// required `FromFFIValue`/`IntoFFIValue`. The macro will convert each
/// argument to the corresponding FFI representation and will call into the host using this FFI
/// representation. On the host each argument is converted back to the native representation and
/// the native implementation is called. Any return value is handled in the same way.
///
/// # Wasm only interfaces
///
/// Some interfaces are only required from within the wasm runtime e.g. the allocator interface.
/// To support this, the macro can be called like `#[runtime_interface(wasm_only)]`. This instructs
/// the macro to make two significant changes to the generated code:
///
/// 1. The generated functions are not callable from the native side.
/// 2. The trait as shown above is not implemented for `Externalities` and is instead implemented
///    for `FunctionExecutor` (from `sp-wasm-interface`).
///
/// # Disable tracing
/// By addding `no_tracing` to the list of options you can prevent the wasm-side interface from
/// generating the default `sp-tracing`-calls. Note that this is rarely needed but only meant for
/// the case when that would create a circular dependency. You usually _do not_ want to add this
/// flag, as tracing doesn't cost you anything by default anyways (it is added as a no-op) but is
/// super useful for debugging later.
///
pub use sp_runtime_interface_proc_macro::runtime_interface;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use sp_externalities::{
	set_and_run_with_externalities, with_externalities, Externalities, ExternalitiesExt, ExtensionStore,
};

#[doc(hidden)]
pub use codec;

pub(crate) mod impls;
#[cfg(feature = "std")]
pub mod host;
#[cfg(any(not(feature = "std"), doc))]
pub mod wasm;
pub mod pass_by;

mod util;

pub use util::{unpack_ptr_and_len, pack_ptr_and_len};

/// Something that can be used by the runtime interface as type to communicate between wasm and the
/// host.
///
/// Every type that should be used in a runtime interface function signature needs to implement
/// this trait.
pub trait RIType {
	/// The ffi type that is used to represent `Self`.
	#[cfg(feature = "std")]
	type FFIType: sp_wasm_interface::IntoValue + sp_wasm_interface::TryFromValue;
	#[cfg(not(feature = "std"))]
	type FFIType;
}

/// A pointer that can be used in a runtime interface function signature.
#[cfg(not(feature = "std"))]
pub type Pointer<T> = *mut T;

/// A pointer that can be used in a runtime interface function signature.
#[cfg(feature = "std")]
pub type Pointer<T> = sp_wasm_interface::Pointer<T>;
