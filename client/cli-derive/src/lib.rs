extern crate proc_macro;

use proc_macro2::{Span};
use proc_macro_error::{abort, abort_call_site, proc_macro_error};
use quote::{quote, ToTokens};
use std::collections::HashMap;
use syn;
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, token::Comma, *};

#[proc_macro_attribute]
#[proc_macro_error]
pub fn spec_factory(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let attrs = match Punctuated::<ExprAssign, Token![,]>::parse_terminated.parse(a) {
		Ok(x) => x,
		Err(err) => abort_call_site!("could not parse attributes: {}", err),
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
	let default_impl_name = std::env::var("CARGO_PKG_NAME").unwrap().to_token_stream();
	let impl_name = attrs.get("impl_name").unwrap_or(&default_impl_name);
	let impl_commit = std::env::var("SUBSTRATE_CLI_COMMIT").unwrap_or_default();
	let commit_dash = if impl_commit.is_empty() { "" } else { "-" };
	let default_impl_version = format!(
		"{}{}{}-{}",
		std::env::var("CARGO_PKG_VERSION").unwrap_or_default(),
		commit_dash,
		impl_commit,
		std::env::var("SUBSTRATE_CLI_PLATFORM").unwrap_or_default(),
	)
	.to_token_stream();
	let impl_version = attrs.get("impl_version").unwrap_or(&default_impl_version);

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

	let gen = quote! {
		impl sc_service::SubstrateCli<#runtime_genesis, #extension> for #cli {
			#s

			fn get_impl_name() -> &'static str { #impl_name }

			fn get_impl_version() -> &'static str { #impl_version }
		}
	};
	gen.into()
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
