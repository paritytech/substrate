// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Proc macro for a npos solution type.

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};

mod assignment;
mod codec;
mod index_assignment;
mod multi_page;
mod single_page;

pub(crate) fn vote_filed(n: usize) -> Ident {
	quote::format_ident!("votes{}", n)
}

pub(crate) fn page_field(page: u8) -> Ident {
	quote::format_ident!("page{}", page)
}

pub(crate) fn syn_err(message: &'static str) -> syn::Error {
	syn::Error::new(Span::call_site(), message)
}

/// Generates a struct to store the election result in a small/compact way. This can encode a
/// structure which is the equivalent of a `sp_npos_elections::Assignment<_>`.
///
/// The following data types can be configured by the macro.
///
/// - The identifier of the voter. This can be any type that supports `parity-scale-codec`'s compact
///   encoding.
/// - The identifier of the target. This can be any type that supports `parity-scale-codec`'s
///   compact encoding.
/// - The accuracy of the ratios. This must be one of the `PerThing` types defined in
///   `sp-arithmetic`.
///
/// Moreover, the maximum number of edges per voter (distribution per assignment) also need to be
/// specified. Attempting to convert from/to an assignment with more distributions will fail.
///
/// For example, the following generates a public struct with name `TestSolution` with `u16` voter
/// type, `u8` target type and `Perbill` accuracy with maximum of 4 edges per voter.
///
/// ```
/// # use sp_npos_elections_solution_type::generate_solution_type;
/// # use sp_arithmetic::per_things::Perbill;
/// generate_solution_type!(pub struct TestSolution::<
///     VoterIndex = u16,
///     TargetIndex = u8,
///     Accuracy = Perbill,
/// >(3));
/// ```
///
/// The output of this macro will roughly look like:
///
/// ```ignore
/// struct TestSolution {
///     voters1: <stripped>
///     voters2: <stripped>
///     voters3: <stripped>
///     voters4: <stripped>
/// }
///
/// impl SolutionBase for TestSolution {};
/// impl Solution for TestSolution {};
/// ```
///
/// The given struct provides function to convert from/to `Assignment` as part of
/// [`sp_npos_elections::Solution`] trait:
///
/// - `fn from_assignment<..>(..)`
/// - `fn into_assignment<..>(..)`
///
/// ## Compact Encoding
///
/// The generated struct is by default deriving both `Encode` and `Decode`. This is okay but could
/// lead to many `0`s in the solution. If prefixed with `#[compact]`, then a custom compact encoding
/// for numbers will be used, similar to how `parity-scale-codec`'s `Compact` works.
///
/// ```
/// # use sp_npos_elections_solution_type::generate_solution_type;
/// # use sp_npos_elections::Solution; // TODO: why is this now needed?
/// # use sp_arithmetic::per_things::Perbill;
/// generate_solution_type!(
///     #[compact]
///     pub struct TestSolutionCompact::<VoterIndex = u16, TargetIndex = u8, Accuracy = Perbill>(8)
/// );
/// ```
///
/// ## Pagination
///
/// All of the above examples generate one struct that implements [`sp_npos_elections::Solution`]
/// and [`sp_npos_elections::SolutionBase`]. These solutions do not have pagination. To support
/// pagination, the `#[pages(_)]` attribute can be used. For example:
///
/// ```
/// # use sp_npos_elections_solution_type::generate_solution_type;
/// # use sp_npos_elections::Solution; // TODO: why is this now needed?
/// # use sp_arithmetic::per_things::Perbill;
/// generate_solution_type!(
///     #[compact]
///     #[pages(3)]
///     pub struct MultiPageSolution::<VoterIndex = u16, TargetIndex = u8, Accuracy = Perbill>(8)
/// );
/// ```
///
/// Will generate two structs:
///
/// 1. `MultiPageSolutionPage` which implements [`sp_npos_elections::Solution`] and
///    [`sp_npos_elections::SolutionBase`].
/// 2. `MultiPageSolution` which implements [`sp_npos_elections::MultiPageSolution`].
///
/// and `MultiPageSolution` wraps 3 pages of `MultiPageSolutionPage`, in other words:
///
/// ```ignore
/// struct MultiPageSolutionPage { ... }
/// struct MultiPageSolution {
/// 	page0: MultiPageSolutionPage { .. },
/// 	page1: MultiPageSolutionPage { .. },
/// 	page2: MultiPageSolutionPage { .. },
/// }
/// ````
/// The page count must always be greater than 2.
#[proc_macro]
pub fn generate_solution_type(item: TokenStream) -> TokenStream {
	let SolutionDef {
		vis,
		ident,
		count,
		voter_pages,
		voter_type,
		target_type,
		weight_type,
		compact_encoding,
	} = syn::parse_macro_input!(item as SolutionDef);

	let imports = imports().unwrap_or_else(|e| e.to_compile_error());

	let def = match voter_pages {
		None => single_page::generate(
			vis.clone(),
			ident.clone(),
			count,
			voter_type.clone(),
			target_type.clone(),
			weight_type.clone(),
			compact_encoding,
		)
		.unwrap_or_else(|e| e.to_compile_error()),
		Some(p) if p >= 2 => {
			let single_page_ident = quote::format_ident!("{}Page", ident);
			let single = single_page::generate(
				vis.clone(),
				single_page_ident.clone(),
				count,
				voter_type.clone(),
				target_type.clone(),
				weight_type.clone(),
				compact_encoding,
			)
			.unwrap_or_else(|e| e.to_compile_error());
			let multi = multi_page::generate(
				vis,
				ident.clone(),
				single_page_ident,
				count,
				p,
				voter_type.clone(),
				target_type.clone(),
				weight_type.clone(),
			)
			.unwrap_or_else(|e| e.to_compile_error());
			quote!(#single #multi)
		},
		_ => syn_err("#[pages(_)] can only accept values larger than 2.").to_compile_error(),
	};

	quote!(
		#imports
		#def
	)
	.into()
}

struct SolutionDef {
	vis: syn::Visibility,
	ident: syn::Ident,
	voter_pages: Option<u8>,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	count: usize,
	compact_encoding: bool,
}

fn check_attributes(input: ParseStream) -> syn::Result<(bool, Option<u8>)> {
	let attrs = input.call(syn::Attribute::parse_outer).unwrap_or_default();
	if attrs.len() > 2 {
		return Err(syn_err("compact solution can accept only #[compact] and #[pages]"))
	}

	let has_compact = attrs.iter().any(|attr| {
		if attr.path.segments.len() == 1 {
			let segment = attr.path.segments.first().expect("Vec with len 1 can be popped.");
			if segment.ident == Ident::new("compact", Span::call_site()) {
				return true
			}
		}
		false
	});

	let mut pages = None;
	for attr in attrs.iter() {
		if attr.path.segments.len() == 1 {
			let segment = attr.path.segments.first().expect("Vec with len 1 can be popped.");
			if segment.ident == Ident::new("pages", Span::call_site()) {
				let tokens = &attr.tokens;
				if let Ok(parsed) = syn::parse2::<syn::ExprParen>(tokens.clone()) {
					if let Ok(parsed_pages) = parse_parenthesized_number::<u8>(parsed) {
						pages = Some(parsed_pages);
					} else {
						return Err(syn_err("Failed to parse a number into u8 in `#[pages(_)]`"))
					}
				} else {
					return Err(syn_err("Failed to parse a number into u8 in `#[pages(_)]`"))
				}
			}
		}
	}

	Ok((has_compact, pages))
}

impl Parse for SolutionDef {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		// optional #[compact] and #[pages(_)]
		let (compact_encoding, voter_pages) = check_attributes(input)?;

		// <vis> struct <name>
		let vis: syn::Visibility = input.parse()?;
		let _ = <syn::Token![struct]>::parse(input)?;
		let ident: syn::Ident = input.parse()?;

		// ::<V, T, W>
		let _ = <syn::Token![::]>::parse(input)?;
		let generics: syn::AngleBracketedGenericArguments = input.parse()?;

		if generics.args.len() != 3 {
			return Err(syn_err("Must provide 3 generic args."))
		}

		let expected_types = ["VoterIndex", "TargetIndex", "Accuracy"];

		let mut types: Vec<syn::Type> = generics
			.args
			.iter()
			.zip(expected_types.iter())
			.map(|(t, expected)| match t {
				syn::GenericArgument::Type(ty) => {
					// this is now an error
					Err(syn::Error::new_spanned(
						ty,
						format!("Expected binding: `{} = ...`", expected),
					))
				},
				syn::GenericArgument::Binding(syn::Binding { ident, ty, .. }) => {
					// check that we have the right keyword for this position in the argument list
					if ident == expected {
						Ok(ty.clone())
					} else {
						Err(syn::Error::new_spanned(ident, format!("Expected `{}`", expected)))
					}
				},
				_ => Err(syn_err("Wrong type of generic provided. Must be a `type`.")),
			})
			.collect::<Result<_>>()?;

		let weight_type = types.pop().expect("Vector of length 3 can be popped; qed");
		let target_type = types.pop().expect("Vector of length 2 can be popped; qed");
		let voter_type = types.pop().expect("Vector of length 1 can be popped; qed");

		// (<count>)
		let count_expr: syn::ExprParen = input.parse()?;
		let count = parse_parenthesized_number::<usize>(count_expr)?;

		Ok(Self {
			vis,
			ident,
			voter_pages,
			voter_type,
			target_type,
			weight_type,
			count,
			compact_encoding,
		})
	}
}

fn parse_parenthesized_number<N: std::str::FromStr>(input_expr: syn::ExprParen) -> syn::Result<N>
where
	<N as std::str::FromStr>::Err: std::fmt::Display,
{
	let expr = input_expr.expr;
	let expr_lit = match *expr {
		syn::Expr::Lit(count_lit) => count_lit.lit,
		_ => return Err(syn_err("Count must be literal.")),
	};
	let int_lit = match expr_lit {
		syn::Lit::Int(int_lit) => int_lit,
		_ => return Err(syn_err("Count must be int literal.")),
	};
	int_lit.base10_parse::<N>()
}

fn imports() -> Result<TokenStream2> {
	match crate_name("sp-npos-elections") {
		Ok(FoundCrate::Itself) => Ok(quote! { use crate as _npos; }),
		Ok(FoundCrate::Name(sp_npos_elections)) => {
			let ident = syn::Ident::new(&sp_npos_elections, Span::call_site());
			Ok(quote!( extern crate #ident as _npos; ))
		},
		Err(e) => Err(syn::Error::new(Span::call_site(), e)),
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn ui_fail() {
		let cases = trybuild::TestCases::new();
		cases.compile_fail("tests/ui/fail/*.rs");
	}
}
