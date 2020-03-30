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
use std::collections::{HashMap, HashSet};
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

macro_rules! define_if_missing {
	(
		$existing_methods:expr, $impl:expr,
		{ fn $method:ident () $(-> $result:ty)? }
	) => {
		if !$existing_methods.contains(stringify!($method)) {
			$impl.items.push(ImplItem::Verbatim(quote! {
				fn $method() $(-> $result)? {
					#$method
				}
			}));
		}
	}
}

pub(crate) fn substrate_cli(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro2::TokenStream {
	let attrs = match Punctuated::<ExprAssign, Token![,]>::parse_terminated.parse(a) {
		Ok(x) => x,
		Err(err) => abort!(err.span(), "could not parse attributes: {}", err),
	};

	let mut attrs = attrs
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

	let pkg_name = std::env::var("CARGO_PKG_NAME").unwrap().to_token_stream();
	let impl_name = attrs
		.remove("impl_name")
		.unwrap_or_else(|| pkg_name.clone());
	let impl_version = attrs
		.remove("impl_version")
		.unwrap_or_else(|| get_version().to_token_stream());
	let support_url = attrs
		.remove("support_url")
		.unwrap_or_else(|| abort_call_site!("missing attribute: support_url"));
	let executable_name = attrs
		.remove("executable_name")
		.unwrap_or_else(|| pkg_name.clone());
	let author = attrs.remove("author").unwrap_or_else(|| {
		std::env::var("CARGO_PKG_AUTHORS")
			.unwrap_or_default()
			.to_token_stream()
	});
	let description = attrs.remove("description").unwrap_or_else(|| {
		std::env::var("CARGO_PKG_DESCRIPTION")
			.unwrap_or_default()
			.to_token_stream()
	});
	let copyright_start_year = attrs
		.remove("copyright_start_year")
		.unwrap_or_else(|| abort_call_site!("missing attribute: copyright_start_year"));

	if !attrs.is_empty() {
		abort_call_site!(
			"unknown macro parameters: {}",
			attrs
				.keys()
				.map(|x| x.as_str())
				.collect::<Vec<_>>()
				.join(", ")
		);
	}

	let mut i: ItemImpl = match syn::parse(i) {
		Ok(x) => x,
		_ => abort_call_site!("this macro only works on an impl"),
	};

	let existing_methods = i
		.items
		.iter()
		.filter_map(|x| match x {
			ImplItem::Method(x) => Some(x.sig.ident.to_string()),
			_ => None,
		})
		.collect::<HashSet<_>>();

	define_if_missing!(existing_methods, i, {
		fn impl_name() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn impl_version() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn support_url() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn executable_name() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn author() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn description() -> &'static str
	});

	define_if_missing!(existing_methods, i, {
		fn copyright_start_year() -> i32
	});

	quote!(#i)
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
	let impl_commit = std::env::var("VERGEN_SHA_SHORT")
		.unwrap_or_else(|_| {
			abort_call_site!("missing env variable VERGEN_SHA_SHORT. You might want to add a build.rs script that runs substrate_build_script_utils::generate_cargo_keys()")
		});
	let commit_dash = if impl_commit.is_empty() { "" } else { "-" };

	format!(
		"{}{}{}-{}",
		std::env::var("CARGO_PKG_VERSION").unwrap_or_default(),
		commit_dash,
		impl_commit,
		get_platform(),
	)
}
