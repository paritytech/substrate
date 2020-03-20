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

use proc_macro2::Span;
use proc_macro_error::{abort, abort_call_site};
use quote::{quote, ToTokens};
use std::collections::HashMap;
use syn;
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, token::Comma, *};

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

	let output = match &s.sig.output {
		ReturnType::Default => abort_call_site!("no return type"),
		ReturnType::Type(_, b) => b,
	};

	let output_ok = match get_type_arguments(output, "Result") {
		Ok(x) => x
			.iter()
			.filter_map(|x| match x {
				GenericArgument::Type(ty) => Some(ty),
				_ => None,
			})
			.next()
			.unwrap(),
		Err(span) => abort!(
			span,
			"expected: Result<Option<sc_service::ChainSpec<_, _>>, String>"
		),
	};

	let output_option = match get_type_arguments(output_ok, "Option") {
		Ok(x) => x
			.iter()
			.filter_map(|x| match x {
				GenericArgument::Type(ty) => Some(ty),
				_ => None,
			})
			.next()
			.unwrap(),
		Err(span) => abort!(span, "expected: Option<sc_service::ChainSpec<_, _>>"),
	};

	let output_chain_spec = match get_type_arguments(output_option, "ChainSpec") {
		Ok(x) => x,
		Err(span) => abort!(span, "expected: sc_service::ChainSpec<_, _>"),
	};

	let type_args = output_chain_spec
		.iter()
		.filter_map(|x| match x {
			GenericArgument::Type(Type::Path(ty_path)) => Some(ty_path),
			_ => None,
		})
		.collect::<Vec<_>>();

	if type_args.is_empty() {
		abort!(
			output_chain_spec.span(),
			"could not find the G type argument of sc_service::ChainSpec"
		);
	}

	let runtime_genesis = type_args[0];
	let extension = type_args.get(1);

	quote! {
		impl ::sc_cli::SubstrateCLI<#runtime_genesis, #extension> for #cli {
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

fn get_type_arguments<'a>(
	ty: &'a Type,
	equal: &str,
) -> std::result::Result<&'a Punctuated<GenericArgument, Comma>, Span> {
	match ty {
		Type::Path(TypePath {
			qself: None,
			path: Path {
				leading_colon: None,
				segments,
			},
		}) => {
			let last_segment = segments.iter().last();

			match last_segment {
				Some(PathSegment {
					ident,
					arguments:
						PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }),
				}) if ident == equal => Ok(args),
				_ => Err(ty.span()),
			}
		}
		_ => Err(ty.span()),
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
