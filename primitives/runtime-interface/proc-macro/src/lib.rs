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

//! This crate provides procedural macros for usage within the context of the Substrate runtime
//! interface.
//!
//! The following macros are provided:
//!
//! 1. The [`#[runtime_interface]`](attr.runtime_interface.html) attribute macro for generating the
//!    runtime interfaces.
//! 2. The [`PassByCodec`](derive.PassByCodec.html) derive macro for implementing `PassBy` with `Codec`.
//! 3. The [`PassByEnum`](derive.PassByInner.html) derive macro for implementing `PassBy` with `Enum`.
//! 4. The [`PassByInner`](derive.PassByInner.html) derive macro for implementing `PassBy` with `Inner`.

extern crate proc_macro;

use syn::{parse_macro_input, ItemTrait, DeriveInput};

mod pass_by;
mod runtime_interface;
mod utils;

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
/// # use runtime_interface::runtime_interface;
///
/// #[runtime_interface]
/// trait Interface {
///     /// A function that can be called from native/wasm.
///     ///
///     /// The implementation given to this function is only compiled on native.
///     fn call_some_complex_code(data: &[u8]) -> Vec<u8> {
///         // Here you could call some rather complex code that only compiles on native or
///         // is way faster in native than executing it in wasm.
///         Vec::new()
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
///         fn call_some_complex_code(data: &[u8]) -> Vec<u8>;
///         fn set_or_clear(&mut self, optional: Option<Vec<u8>>);
///     }
///
///     impl Interface for &mut dyn externalities::Externalities {
///         fn call_some_complex_code(data: &[u8]) -> Vec<u8> { Vec::new() }
///         fn set_or_clear(&mut self, optional: Option<Vec<u8>>) {
///             match optional {
///                 Some(value) => self.set_storage([1, 2, 3, 4].to_vec(), value),
///                 None => self.clear_storage(&[1, 2, 3, 4]),
///             }
///         }
///     }
///
///     pub fn call_some_complex_code(data: &[u8]) -> Vec<u8> {
///         <&mut dyn externalities::Externalities as Interface>::call_some_complex_code(data)
///     }
///
///     pub fn set_or_clear(optional: Option<Vec<u8>>) {
///         externalities::with_externalities(|mut ext| Interface::set_or_clear(&mut ext, optional))
///             .expect("`set_or_clear` called outside of an Externalities-provided environment.")
///     }
///
///     /// This type implements the `HostFunctions` trait (from `substrate-wasm-interface`) and
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
///             pub fn ext_Interface_call_some_complex_code_version_1(data: u64) -> u64;
///             /// `optional` holds the pointer and the length of the encoded value.
///             pub fn ext_Interface_set_or_clear_version_1(optional: u64);
///         }
///     }
///
///     /// The type is actually `ExchangeableFunction` (from `substrate-runtime-interface`).
///     ///
///     /// This can be used to replace the implementation of the `call_some_complex_code` function.
///     /// Instead of calling into the host, the callee will automatically call the other
///     /// implementation.
///     ///
///     /// To replace the implementation:
///     ///
///     /// `host_call_some_complex_code.replace_implementation(some_other_impl)`
///     pub static host_call_some_complex_code: () = ();
///     pub static host_set_or_clear: () = ();
///
///     pub fn call_some_complex_code(data: &[u8]) -> Vec<u8> {
///         // This is the actual call: `host_call_some_complex_code.get()(data)`
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
/// The macro supports any kind of argument type, as long as it implements `RIType` and the required
/// `FromFFIValue`/`IntoFFIValue` from `substrate-runtime-interface`. The macro will convert each
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
///    for `FunctionExecutor` (from `substrate-wasm-interface`).
#[proc_macro_attribute]
pub fn runtime_interface(
	attrs: proc_macro::TokenStream,
	input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let trait_def = parse_macro_input!(input as ItemTrait);
	let wasm_only = parse_macro_input!(attrs as Option<runtime_interface::keywords::wasm_only>);

	runtime_interface::runtime_interface_impl(trait_def, wasm_only.is_some())
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

/// Derive macro for implementing `PassBy` with the `Codec` strategy.
///
/// This requires that the type implements `Encode` and `Decode` from `parity-scale-codec`.
///
/// # Example
///
/// ```
/// # use runtime_interface::pass_by::PassByCodec;
/// # use codec::{Encode, Decode};
/// #[derive(PassByCodec, Encode, Decode)]
/// struct EncodableType {
///     name: Vec<u8>,
///     param: u32,
/// }
/// ```
#[proc_macro_derive(PassByCodec)]
pub fn pass_by_codec(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::codec_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}

/// Derive macro for implementing `PassBy` with the `Inner` strategy.
///
/// Besides implementing `PassBy`, this derive also implements the helper trait `PassByInner`.
///
/// The type is required to be a struct with just one field. The field type needs to implement
/// the required traits to pass it between the wasm and the native side. (See the runtime interface
/// crate for more information about these traits.)
///
/// # Example
///
/// ```
/// # use runtime_interface::pass_by::PassByInner;
/// #[derive(PassByInner)]
/// struct Data([u8; 32]);
/// ```
///
/// ```
/// # use runtime_interface::pass_by::PassByInner;
/// #[derive(PassByInner)]
/// struct Data {
///     data: [u8; 32],
/// }
/// ```
#[proc_macro_derive(PassByInner)]
pub fn pass_by_inner(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::inner_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}

/// Derive macro for implementing `PassBy` with the `Enum` strategy.
///
/// Besides implementing `PassBy`, this derive also implements `TryFrom<u8>` and `From<Self> for u8`
/// for the type.
///
/// The type is required to be an enum with only unit variants and at maximum `256` variants. Also
/// it is required that the type implements `Copy`.
///
/// # Example
///
/// ```
/// # use runtime_interface::pass_by::PassByEnum;
/// #[derive(PassByEnum, Copy, Clone)]
/// enum Data {
///     Okay,
///     NotOkay,
///     // This will not work with the derive.
///     //Why(u32),
/// }
/// ```
#[proc_macro_derive(PassByEnum)]
pub fn pass_by_enum(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::enum_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}
