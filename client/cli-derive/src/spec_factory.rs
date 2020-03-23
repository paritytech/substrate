// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Configuration trait for a CLI based on substrate

use proc_macro_error::{abort, abort_call_site};
use quote::{quote, ToTokens};
use std::collections::HashMap;
use syn;
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

pub(crate) fn spec_factory(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro2::TokenStream {
	let attrs = match Punctuated::<ExprAssign, Token![,]>::parse_terminated.parse(a) {
		Ok(x) => x,
		Err(err) => abort!(err.span(), "could not parse attributes: {}", err),
	};

	let attrs = attrs
		.iter()
		.map(|x| {
			(
				match &*x.left {
					Expr::Path(p) if p.path.segments.len() == 1 => {
						p.path.segments[0].ident.to_string()
					}
					_ => abort!(x.left.span(), "could not parse token"),
				},
				(*x.right).to_token_stream(),
			)
		})
		.collect::<HashMap<_, _>>();

	let default_cli = quote! { Cli };
	let cli = attrs.get("cli").unwrap_or(&default_cli);
	let pkg_name = std::env::var("CARGO_PKG_NAME").unwrap().to_token_stream();
	let impl_name = attrs.get("impl_name").unwrap_or(&pkg_name);
	let default_impl_version = get_version().to_token_stream();
	let impl_version = attrs.get("impl_version").unwrap_or(&default_impl_version);
	let support_url = attrs
		.get("support_url")
		.unwrap_or_else(|| abort_call_site!("missing attribute: support_url"));
	let executable_name = attrs.get("executable_name").unwrap_or(&pkg_name);
	let default_author = std::env::var("CARGO_PKG_AUTHORS")
		.unwrap_or_default()
		.to_token_stream();
	let author = attrs.get("author").unwrap_or(&default_author);
	let default_description = std::env::var("CARGO_PKG_DESCRIPTION")
		.unwrap_or_default()
		.to_token_stream();
	let description = attrs.get("description").unwrap_or(&default_description);
	let copyright_start_year = attrs
		.get("copyright_start_year")
		.unwrap_or_else(|| abort_call_site!("missing attribute: copyright_start_year"));

	let s: ItemFn = match syn::parse(i) {
		Ok(x) => x,
		_ => abort_call_site!("this macro only works on a function"),
	};

	quote! {
		impl ::sc_cli::SubstrateCLI for #cli {
			#s

			fn get_impl_name() -> &'static str { #impl_name }
			fn get_impl_version() -> &'static str { #impl_version }
			fn get_support_url() -> &'static str { #support_url }
			fn get_executable_name() -> &'static str { #executable_name }
			fn get_author() -> &'static str { #author }
			fn get_description() -> &'static str { #description }
			fn get_copyright_start_year() -> i32 { #copyright_start_year }
		}
	}
}

fn get_platform() -> String {
	use platforms::*;

	let env_dash = if TARGET_ENV.is_some() { "-" } else { "" };

	format!(
		"{}-{}{}{}",
		TARGET_ARCH.as_str(),
		TARGET_OS.as_str(),
		env_dash,
		TARGET_ENV.map(|x| x.as_str()).unwrap_or(""),
	)
}

fn get_version() -> String {
	let impl_commit = std::env::var("VERGEN_SHA_SHORT").unwrap_or_default();
	let commit_dash = if impl_commit.is_empty() { "" } else { "-" };

	format!(
		"{}{}{}-{}",
		std::env::var("CARGO_PKG_VERSION").unwrap_or_default(),
		commit_dash,
		impl_commit,
		get_platform(),
	)
}
