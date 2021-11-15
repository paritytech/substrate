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

//! This crate provides procedural macros for usage within the context of the Substrate runtime
//! interface.
//!
//! The following macros are provided:
//!
//! 1. The [`#[runtime_interface]`](attr.runtime_interface.html) attribute macro for generating the
//!    runtime interfaces.
//! 2. The [`PassByCodec`](derive.PassByCodec.html) derive macro for implementing `PassBy` with
//! `Codec`. 3. The [`PassByEnum`](derive.PassByInner.html) derive macro for implementing `PassBy`
//! with `Enum`. 4. The [`PassByInner`](derive.PassByInner.html) derive macro for implementing
//! `PassBy` with `Inner`.

use syn::{
	parse::{Parse, ParseStream},
	parse_macro_input, DeriveInput, Error, ItemTrait, Result, Token,
};

mod pass_by;
mod runtime_interface;
mod utils;

struct Options {
	wasm_only: bool,
	tracing: bool,
	feature_force_version: Vec<(String, String, u32)>,
}

impl Options {
	fn unpack(self) -> (bool, bool, Vec<(String, String, u32)>) {
		(self.wasm_only, self.tracing, self.feature_force_version)
	}
}
impl Default for Options {
	fn default() -> Self {
		Options { wasm_only: false, tracing: true, feature_force_version: Vec::new() }
	}
}

impl Parse for Options {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut res = Self::default();
		while !input.is_empty() {
			let lookahead = input.lookahead1();
			if lookahead.peek(runtime_interface::keywords::wasm_only) {
				let _ = input.parse::<runtime_interface::keywords::wasm_only>();
				res.wasm_only = true;
			} else if lookahead.peek(runtime_interface::keywords::no_tracing) {
				let _ = input.parse::<runtime_interface::keywords::no_tracing>();
				res.tracing = false;
			} else if lookahead.peek(runtime_interface::keywords::feature_force_version) {
				let _ = input.parse::<runtime_interface::keywords::feature_force_version>();
				let _ = input.parse::<Token![=]>();
				let feature_name = input.parse::<syn::Ident>()?;
				let _ = input.parse::<Token![,]>();
				let func_name = input.parse::<syn::Ident>()?;
				let _ = input.parse::<Token![,]>();
				let func_version = match input.parse::<syn::ExprLit>()? {
					syn::ExprLit { lit: syn::Lit::Int(lit), .. } => lit.base10_parse::<u32>()?,
					_ => return Err(Error::new(input.span(), "Expected u32 integer as version.")),
				};
				let patch = (feature_name.to_string(), func_name.to_string(), func_version);
				res.feature_force_version.push(patch);
			} else if lookahead.peek(Token![,]) {
				let _ = input.parse::<Token![,]>();
			} else {
				return Err(lookahead.error())
			}
		}
		Ok(res)
	}
}

#[proc_macro_attribute]
pub fn runtime_interface(
	attrs: proc_macro::TokenStream,
	input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let trait_def = parse_macro_input!(input as ItemTrait);
	let (wasm_only, tracing, feature_force_version) = parse_macro_input!(attrs as Options).unpack();

	runtime_interface::runtime_interface_impl(trait_def, wasm_only, tracing, feature_force_version)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

#[proc_macro_derive(PassByCodec)]
pub fn pass_by_codec(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::codec_derive_impl(input)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

#[proc_macro_derive(PassByInner)]
pub fn pass_by_inner(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::inner_derive_impl(input)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

#[proc_macro_derive(PassByEnum)]
pub fn pass_by_enum(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	pass_by::enum_derive_impl(input).unwrap_or_else(|e| e.to_compile_error()).into()
}
