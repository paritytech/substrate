#![allow(unused_imports, unused_variables)]

extern crate proc_macro;

use proc_macro2::{Span, TokenStream};
use proc_macro_error::{abort, abort_call_site, proc_macro_error, set_dummy};
use quote::{quote, quote_spanned};
use syn;
use syn::parse::Parse;
use syn::parse::ParseStream;
use syn::parse_macro_input;
use syn::{parse_quote, Token};
use syn::{punctuated::Punctuated, spanned::Spanned, token::Comma, *};

#[proc_macro_attribute]
#[proc_macro_error]
pub fn spec_factory(
	_a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let s: syn::ItemFn = match syn::parse(i) {
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
		Err(span) => abort!(span, "expected: Result<Option<ChainSpec<_, _>>, String>"),
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
		Err(span) => abort!(span, "expected: Option<ChainSpec<_, _>>"),
	};

	let output_chain_spec = match get_type_arguments(output_option, "ChainSpec") {
		Ok(x) => x,
		Err(span) => abort!(span, "expected: ChainSpec<_, _>"),
	};

	let type_args = output_chain_spec
		.iter()
		.map(|x| match x {
			GenericArgument::Type(Type::Path(ty_path)) => Some(ty_path),
			_ => None,
		})
		.collect::<Vec<_>>();

	if type_args.is_empty() {
		abort!(
			output_chain_spec.span(),
			"could not find the G type argument of ChainSpec"
		);
	}

	let runtime_genesis = type_args[0];
	let extension = type_args.get(1);

	let gen = quote! {
		impl sc_service::SubstrateCli<#runtime_genesis, #extension> for Cli {
			#s
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
