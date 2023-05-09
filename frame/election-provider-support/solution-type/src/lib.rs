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

//! Proc macro for a npos solution type.

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};

mod codec;
mod from_assignment_helpers;
mod index_assignment;
mod single_page;

/// Get the name of a filed based on voter count.
pub(crate) fn vote_field(n: usize) -> Ident {
	quote::format_ident!("votes{}", n)
}

/// Generate a `syn::Error`.
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
/// - The maximum number of voters. This must be of type `Get<u32>`. Check <https://github.com/paritytech/substrate/issues/10866>
///   for more details. This is used to bound the struct, by leveraging the fact that `votes1.len()
///   < votes2.len() < ... < votesn.len()` (the details of the struct is explained further below).
///   We know that `sum_i votes_i.len() <= MaxVoters`, and we know that the maximum size of the
///   struct would be achieved if all voters fall in the last bucket. One can also check the tests
///   and more specifically `max_encoded_len_exact` for a concrete example.
///
/// Moreover, the maximum number of edges per voter (distribution per assignment) also need to be
/// specified. Attempting to convert from/to an assignment with more distributions will fail.
///
/// For example, the following generates a public struct with name `TestSolution` with `u16` voter
/// type, `u8` target type and `Perbill` accuracy with maximum of 4 edges per voter.
///
/// ```
/// # use frame_election_provider_solution_type::generate_solution_type;
/// # use sp_arithmetic::per_things::Perbill;
/// # use frame_support::traits::ConstU32;
/// generate_solution_type!(pub struct TestSolution::<
///     VoterIndex = u16,
///     TargetIndex = u8,
///     Accuracy = Perbill,
///     MaxVoters = ConstU32::<10>,
/// >(4));
/// ```
///
/// The output of this macro will roughly look like:
///
/// ```ignore
/// struct TestSolution {
/// 	voters1: vec![(u16 /* voter */, u8 /* target */)]
/// 	voters2: vec![
/// 		(u16 /* voter */, [u8 /* first target*/, Perbill /* proportion for first target */], u8 /* last target */)
/// 	]
/// 	voters3: vec![
/// 		(u16 /* voter */,  [
/// 			(u8 /* first target*/, Perbill /* proportion for first target */ ),
/// 			(u8 /* second target */, Perbill /* proportion for second target*/)
/// 		], u8 /* last target */)
/// 		],
/// 	voters4: ...,
/// }
///
/// impl NposSolution for TestSolution {};
/// impl Solution for TestSolution {};
/// ```
///
/// The given struct provides function to convert from/to `Assignment` as part of
/// `frame_election_provider_support::NposSolution` trait:
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
/// # use frame_election_provider_solution_type::generate_solution_type;
/// # use frame_election_provider_support::NposSolution;
/// # use sp_arithmetic::per_things::Perbill;
/// # use frame_support::traits::ConstU32;
/// generate_solution_type!(
///     #[compact]
///     pub struct TestSolutionCompact::<
///          VoterIndex = u16,
///          TargetIndex = u8,
///          Accuracy = Perbill,
///          MaxVoters = ConstU32::<10>,
///     >(8)
/// );
/// ```
#[proc_macro]
pub fn generate_solution_type(item: TokenStream) -> TokenStream {
	let solution_def = syn::parse_macro_input!(item as SolutionDef);

	let imports = imports().unwrap_or_else(|e| e.to_compile_error());

	let def = single_page::generate(solution_def).unwrap_or_else(|e| e.to_compile_error());

	quote!(
		#imports
		#def
	)
	.into()
}

struct SolutionDef {
	vis: syn::Visibility,
	ident: syn::Ident,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	max_voters: syn::Type,
	count: usize,
	compact_encoding: bool,
}

fn check_attributes(input: ParseStream) -> syn::Result<bool> {
	let mut attrs = input.call(syn::Attribute::parse_outer).unwrap_or_default();
	if attrs.len() > 1 {
		let extra_attr = attrs.pop().expect("attributes vec with len > 1 can be popped");
		return Err(syn::Error::new_spanned(
			extra_attr,
			"compact solution can accept only #[compact]",
		))
	}
	if attrs.is_empty() {
		return Ok(false)
	}
	let attr = attrs.pop().expect("attributes vec with len 1 can be popped.");
	if attr.path().is_ident("compact") {
		Ok(true)
	} else {
		Err(syn::Error::new_spanned(attr, "compact solution can accept only #[compact]"))
	}
}

impl Parse for SolutionDef {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		// optional #[compact]
		let compact_encoding = check_attributes(input)?;

		// <vis> struct <name>
		let vis: syn::Visibility = input.parse()?;
		let _ = <syn::Token![struct]>::parse(input)?;
		let ident: syn::Ident = input.parse()?;

		// ::<V, T, W>
		let _ = <syn::Token![::]>::parse(input)?;
		let generics: syn::AngleBracketedGenericArguments = input.parse()?;

		if generics.args.len() != 4 {
			return Err(syn_err("Must provide 4 generic args."))
		}

		let expected_types = ["VoterIndex", "TargetIndex", "Accuracy", "MaxVoters"];

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
				syn::GenericArgument::AssocType(syn::AssocType { ident, ty, .. }) => {
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

		let max_voters = types.pop().expect("Vector of length 4 can be popped; qed");
		let weight_type = types.pop().expect("Vector of length 3 can be popped; qed");
		let target_type = types.pop().expect("Vector of length 2 can be popped; qed");
		let voter_type = types.pop().expect("Vector of length 1 can be popped; qed");

		// (<count>)
		let count_expr: syn::ExprParen = input.parse()?;
		let count = parse_parenthesized_number::<usize>(count_expr)?;

		Ok(Self {
			vis,
			ident,
			voter_type,
			target_type,
			weight_type,
			max_voters,
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
	match crate_name("frame-election-provider-support") {
		Ok(FoundCrate::Itself) => Ok(quote! { use crate as _feps; }),
		Ok(FoundCrate::Name(frame_election_provider_support)) => {
			let ident = syn::Ident::new(&frame_election_provider_support, Span::call_site());
			Ok(quote!( extern crate #ident as _feps; ))
		},
		Err(e) => Err(syn::Error::new(Span::call_site(), e)),
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn ui_fail() {
		// Only run the ui tests when `RUN_UI_TESTS` is set.
		if std::env::var("RUN_UI_TESTS").is_err() {
			return
		}

		let cases = trybuild::TestCases::new();
		cases.compile_fail("tests/ui/fail/*.rs");
	}
}
