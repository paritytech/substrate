// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use proc_macro::{Span, TokenStream};
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;

#[proc_macro_attribute]
pub fn test(args: TokenStream, item: TokenStream) -> TokenStream {
	let input = syn::parse_macro_input!(item as syn::ItemFn);

	parse_knobs(input, args.into()).unwrap_or_else(|e| e.to_compile_error().into())
}

fn parse_knobs(
	mut input: syn::ItemFn,
	args: proc_macro2::TokenStream,
) -> Result<TokenStream, syn::Error> {
	let sig = &mut input.sig;
	let body = &input.block;
	let attrs = &input.attrs;
	let vis = input.vis;

	if !sig.inputs.is_empty() {
		return Err(syn::Error::new_spanned(&sig, "No arguments expected for tests."))
	}

	let crate_name = match crate_name("substrate-test-utils") {
		Ok(FoundCrate::Itself) => syn::Ident::new("substrate_test_utils", Span::call_site().into()),
		Ok(FoundCrate::Name(crate_name)) => syn::Ident::new(&crate_name, Span::call_site().into()),
		Err(e) => return Err(syn::Error::new_spanned(&sig, e)),
	};

	let header = {
		quote! {
			#[#crate_name::tokio::test( #args )]
		}
	};

	let result = quote! {
		#header
		#(#attrs)*
		#vis #sig {
			if #crate_name::tokio::time::timeout(
				std::time::Duration::from_secs(
					std::env::var("SUBSTRATE_TEST_TIMEOUT")
						.ok()
						.and_then(|x| x.parse().ok())
						.unwrap_or(600)),
				async move { #body },
			).await.is_err() {
				panic!("The test took too long!");
			}
		}
	};

	Ok(result.into())
}
