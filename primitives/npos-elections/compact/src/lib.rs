// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Proc macro for a npos compact assignment.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Span, Ident};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::{parse::{Parse, ParseStream, Result}};

mod assignment;
mod codec;

// prefix used for struct fields in compact.
const PREFIX: &'static str = "votes";

pub(crate) fn syn_err(message: &'static str) -> syn::Error {
	syn::Error::new(Span::call_site(), message)
}

/// Generates a struct to store the election result in a small way. This can encode a structure
/// which is the equivalent of a `sp_npos_elections::Assignment<_>`.
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
///
/// For example, the following generates a public struct with name `TestSolution` with `u16` voter
/// type, `u8` target type and `Perbill` accuracy with maximum of 8 edges per voter.
///
/// ```ignore
/// generate_solution_type!(pub struct TestSolution<u16, u8, Perbill>::(8))
/// ```
///
/// The given struct provides function to convert from/to Assignment:
///
/// - [`from_assignment()`].
/// - [`fn into_assignment()`].
///
/// The generated struct is by default deriving both `Encode` and `Decode`. This is okay but could
/// lead to many 0s in the solution. If prefixed with `#[compact]`, then a custom compact encoding
/// for numbers will be used, similar to how `parity-scale-codec`'s `Compact` works.
///
/// ```ignore
/// generate_solution_type!(
///     #[compact]
///     pub struct TestSolutionCompact<u16, u8, Perbill>::(8)
/// )
/// ```
#[proc_macro]
pub fn generate_solution_type(item: TokenStream) -> TokenStream {
	let SolutionDef {
		vis,
		ident,
		count,
		voter_type,
		target_type,
		weight_type,
		compact_encoding,
	} = syn::parse_macro_input!(item as SolutionDef);

	let imports = imports().unwrap_or_else(|e| e.to_compile_error());

	let solution_struct = struct_def(
		vis,
		ident.clone(),
		count,
		voter_type.clone(),
		target_type.clone(),
		weight_type.clone(),
		compact_encoding,
	).unwrap_or_else(|e| e.to_compile_error());

	let assignment_impls = assignment::assignment(
		ident.clone(),
		voter_type.clone(),
		target_type.clone(),
		weight_type.clone(),
		count,
	);

	quote!(
		#imports
		#solution_struct
		#assignment_impls
	).into()
}

fn struct_def(
	vis: syn::Visibility,
	ident: syn::Ident,
	count: usize,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	compact_encoding: bool,
) -> Result<TokenStream2> {
	if count <= 2 {
		Err(syn_err("cannot build compact solution struct with capacity less than 3."))?
	}

	let singles = {
		let name = field_name_for(1);
		quote!(
			#name: Vec<(#voter_type, #target_type)>,
		)
	};

	let doubles = {
		let name = field_name_for(2);
		quote!(
			#name: Vec<(#voter_type, (#target_type, #weight_type), #target_type)>,
		)
	};

	let rest = (3..=count).map(|c| {
		let field_name = field_name_for(c);
		let array_len = c - 1;
		quote!(
			#field_name: Vec<(
				#voter_type,
				[(#target_type, #weight_type); #array_len],
				#target_type
			)>,
		)
	}).collect::<TokenStream2>();


	let len_impl = (1..=count).map(|c| {
		let field_name = field_name_for(c);
		quote!(
			all_len = all_len.saturating_add(self.#field_name.len());
		)
	}).collect::<TokenStream2>();

	let edge_count_impl = (1..count).map(|c| {
		let field_name = field_name_for(c);
		quote!(
			all_edges = all_edges.saturating_add(
				self.#field_name.len().saturating_mul(#c as usize)
			);
		)
	}).collect::<TokenStream2>();

	let derives_and_maybe_compact_encoding = if compact_encoding {
		// custom compact encoding.
		let compact_impl = codec::codec_impl(
			ident.clone(),
			voter_type.clone(),
			target_type.clone(),
			weight_type.clone(),
			count,
		);
		quote!{
			#compact_impl
			#[derive(Default, PartialEq, Eq, Clone, Debug)]
		}
	} else {
		// automatically derived.
		quote!(#[derive(Default, PartialEq, Eq, Clone, Debug, _npos::codec::Encode, _npos::codec::Decode)])
	};

	Ok(quote! (
		/// A struct to encode a election assignment in a compact way.
		#derives_and_maybe_compact_encoding
		#vis struct #ident { #singles #doubles #rest }

		impl _npos::VotingLimit for #ident {
			const LIMIT: usize = #count;
		}

		impl #ident {
			/// Get the length of all the assignments that this type is encoding. This is basically
			/// the same as the number of assignments, or the number of voters in total.
			pub fn len(&self) -> usize {
				let mut all_len = 0usize;
				#len_impl
				all_len
			}

			/// Get the total count of edges.
			pub fn edge_count(&self) -> usize {
				let mut all_edges = 0usize;
				#edge_count_impl
				all_edges
			}

			/// Get the average edge count.
			pub fn average_edge_count(&self) -> usize {
				self.edge_count().checked_div(self.len()).unwrap_or(0)
			}
		}
	))
}

fn imports() -> Result<TokenStream2> {
	if std::env::var("CARGO_PKG_NAME").unwrap() == "sp-npos-elections" {
		Ok(quote! {
			use crate as _npos;
		})
	} else {
		match crate_name("sp-npos-elections") {
			Ok(sp_npos_elections) => {
				let ident = syn::Ident::new(&sp_npos_elections, Span::call_site());
				Ok(quote!( extern crate #ident as _npos; ))
			},
			Err(e) => Err(syn::Error::new(Span::call_site(), &e)),
		}
	}
}

struct SolutionDef {
	vis: syn::Visibility,
	ident: syn::Ident,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	count: usize,
	compact_encoding: bool,
}

fn check_compact_attr(input: ParseStream) -> Result<bool> {
	let mut attrs = input.call(syn::Attribute::parse_outer).unwrap_or_default();
	if attrs.len() == 1 {
		let attr = attrs.pop().expect("Vec with len 1 can be popped.");
		if attr.path.segments.len() == 1 {
			let segment = attr.path.segments.first().expect("Vec with len 1 can be popped.");
			if segment.ident == Ident::new("compact", Span::call_site()) {
				Ok(true)
			} else {
				Err(syn_err("generate_solution_type macro can only accept #[compact] attribute."))
			}
		} else {
			Err(syn_err("generate_solution_type macro can only accept #[compact] attribute."))
		}
	} else {
		Ok(false)
	}
}

/// #[compact] pub struct CompactName::<u32, u32, u32>()
impl Parse for SolutionDef {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		// optional #[compact]
		let compact_encoding = check_compact_attr(input)?;

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

		let mut types: Vec<syn::Type> = generics.args.iter().map(|t|
			match t {
				syn::GenericArgument::Type(ty) => Ok(ty.clone()),
				_ => Err(syn_err("Wrong type of generic provided. Must be a `type`.")),
			}
		).collect::<Result<_>>()?;

		let weight_type = types.pop().expect("Vector of length 3 can be popped; qed");
		let target_type = types.pop().expect("Vector of length 2 can be popped; qed");
		let voter_type = types.pop().expect("Vector of length 1 can be popped; qed");

		// (<count>)
		let count_expr: syn::ExprParen = input.parse()?;
		let expr = count_expr.expr;
		let expr_lit = match *expr {
			syn::Expr::Lit(count_lit) => count_lit.lit,
			_ => return Err(syn_err("Count must be literal."))
		};
		let int_lit = match expr_lit {
			syn::Lit::Int(int_lit) => int_lit,
			_ => return Err(syn_err("Count must be int literal."))
		};
		let count = int_lit.base10_parse::<usize>()?;

		Ok(Self { vis, ident, voter_type, target_type, weight_type, count, compact_encoding } )
	}
}

fn field_name_for(n: usize) -> Ident {
	Ident::new(&format!("{}{}", PREFIX, n), Span::call_site())
}
