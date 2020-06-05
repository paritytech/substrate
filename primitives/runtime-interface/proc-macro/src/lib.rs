// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
