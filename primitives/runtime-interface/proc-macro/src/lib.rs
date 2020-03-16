// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

#[proc_macro_derive(PassByCodec)]
pub fn pass_by_codec(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::codec_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}

#[proc_macro_derive(PassByInner)]
pub fn pass_by_inner(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::inner_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}

#[proc_macro_derive(PassByEnum)]
pub fn pass_by_enum(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::enum_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}
