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

//! Procedural macros for generating runtime interfaces.

extern crate proc_macro;

use syn::{parse_macro_input, ItemTrait, DeriveInput};

mod pass_by;
mod runtime_interface;
mod utils;

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
/// # use substrate_runtime_interface::pass_by::PassByCodec;
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
/// # use substrate_runtime_interface::pass_by::PassByInner;
/// #[derive(PassByInner)]
/// struct Data([u8; 32]);
/// ```
///
/// ```
/// # use substrate_runtime_interface::pass_by::PassByInner;
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
/// # use substrate_runtime_interface::pass_by::PassByEnum;
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
