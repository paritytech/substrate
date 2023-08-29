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

//! Implementation of the `create_tt_return_macro` macro

use crate::COUNTER;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Ident, TokenStream};
use quote::format_ident;

struct CreateTtReturnMacroDef {
	name: Ident,
	args: Vec<(Ident, TokenStream)>,
}

impl syn::parse::Parse for CreateTtReturnMacroDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let name = input.parse()?;
		let _ = input.parse::<syn::Token![,]>()?;

		let mut args = Vec::new();
		while !input.is_empty() {
			let mut value;
			let key: Ident = input.parse()?;
			let _ = input.parse::<syn::Token![=]>()?;
			let _: syn::token::Bracket = syn::bracketed!(value in input);
			let _: syn::token::Brace = syn::braced!(value in value);
			let value: TokenStream = value.parse()?;

			args.push((key, value))
		}

		Ok(Self { name, args })
	}
}

/// A proc macro that accepts a name and any number of key-value pairs, to be used to create a
/// declarative macro that follows tt-call conventions and simply calls
/// [`tt_call::tt_return`], accepting an optional `frame-support` argument and returning
/// the key-value pairs that were supplied to the proc macro.
///
/// # Example
/// ```ignore
/// __create_tt_macro! {
///     my_tt_macro,
///     foo = [{ bar }]
/// }
///
/// // Creates the following declarative macro:
///
/// macro_rules! my_tt_macro {
///     {
///         $caller:tt
///         $(frame_support = [{ $($frame_support:ident)::* }])?
///     } => {
///         frame_support::__private::tt_return! {
///             $caller
///             foo = [{ bar }]
///         }
///     }
/// }
/// ```
pub fn create_tt_return_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let CreateTtReturnMacroDef { name, args } =
		syn::parse_macro_input!(input as CreateTtReturnMacroDef);

	let frame_support = match generate_crate_access_2018("frame-support") {
		Ok(i) => i,
		Err(e) => return e.into_compile_error().into(),
	};
	let (keys, values): (Vec<_>, Vec<_>) = args.into_iter().unzip();
	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let unique_name = format_ident!("{}_{}", name, count);

	let decl_macro = quote::quote! {
		#[macro_export]
		#[doc(hidden)]
		macro_rules! #unique_name {
			{
				$caller:tt
				$(frame_support = [{ $($frame_support:ident)::* }])?
			} => {
				#frame_support::__private::tt_return! {
					$caller
					#(
						#keys = [{ #values }]
					)*
				}
			}
		}

		pub use #unique_name as #name;
	};

	decl_macro.into()
}
