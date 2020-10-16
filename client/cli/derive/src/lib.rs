// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::crate_name;
use quote::quote;
use syn::{Error, Expr, Ident, ItemFn};

#[proc_macro_attribute]
pub fn substrate_cli_node_name(arg: TokenStream, item: TokenStream) -> TokenStream {
	let item_fn = syn::parse_macro_input!(item as ItemFn);

	if arg.is_empty() {
		return Error::new(Span::call_site(), "missing expression (name of the node)")
			.to_compile_error()
			.into();
	}

	let name = syn::parse_macro_input!(arg as Expr);

	let crate_name = if std::env::var("CARGO_PKG_NAME").unwrap() == "sc-cli" {
		Ident::new("sc_cli", Span::call_site().into())
	} else {
		let crate_name = match crate_name("sc-cli") {
			Ok(x) => x,
			Err(err) => return Error::new(Span::call_site(), err).to_compile_error().into(),
		};

		Ident::new(&crate_name, Span::call_site().into())
	};

	let ItemFn {
		attrs,
		vis,
		sig,
		block,
	} = item_fn;

	(quote! {
		#(#attrs)*
		#vis #sig {
			let span = #crate_name::tracing::info_span!("substrate-node", name = #name);
			let _enter = span.enter();

			#block
		}
	})
	.into()
}
