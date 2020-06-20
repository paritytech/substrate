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
use syn::{GenericArgument, Type, parse::{Parse, ParseStream, Result}};

mod assignment;
mod staked;

// prefix used for struct fields in compact.
const PREFIX: &'static str = "votes";

/// Generates a struct to store the election assignments in a compact way. The struct can only store
/// distributions up to the given input count. The given count must be greater than 2.
///
/// ```ignore
/// // generate a struct with nominator and edge weight u128, with maximum supported
/// // edge per voter of 16.
/// generate_compact_solution_type(pub TestCompact, 16)
/// ```
///
/// This generates:
///
/// ```ignore
/// pub struct TestCompact<V, T, W> {
/// 	votes1: Vec<(V, T)>,
/// 	votes2: Vec<(V, (T, W), T)>,
/// 	votes3: Vec<(V, [(T, W); 2usize], T)>,
/// 	votes4: Vec<(V, [(T, W); 3usize], T)>,
/// 	votes5: Vec<(V, [(T, W); 4usize], T)>,
/// 	votes6: Vec<(V, [(T, W); 5usize], T)>,
/// 	votes7: Vec<(V, [(T, W); 6usize], T)>,
/// 	votes8: Vec<(V, [(T, W); 7usize], T)>,
/// 	votes9: Vec<(V, [(T, W); 8usize], T)>,
/// 	votes10: Vec<(V, [(T, W); 9usize], T)>,
/// 	votes11: Vec<(V, [(T, W); 10usize], T)>,
/// 	votes12: Vec<(V, [(T, W); 11usize], T)>,
/// 	votes13: Vec<(V, [(T, W); 12usize], T)>,
/// 	votes14: Vec<(V, [(T, W); 13usize], T)>,
/// 	votes15: Vec<(V, [(T, W); 14usize], T)>,
/// 	votes16: Vec<(V, [(T, W); 15usize], T)>,
/// }
/// ```
///
/// The generic arguments are:
/// - `V`: identifier/index for voter (nominator) types.
/// - `T` identifier/index for candidate (validator) types.
/// - `W` weight type.
///
/// Some conversion implementations are provided by default if
/// - `W` is u128, or
/// - `W` is anything that implements `PerThing` (such as `Perbill`)
///
/// The ideas behind the structure are as follows:
///
/// - For single distribution, no weight is stored. The weight is known to be 100%.
/// - For all the rest, the weight if the last distribution is omitted. This value can be computed
///   from the rest.
///
#[proc_macro]
pub fn generate_compact_solution_type(item: TokenStream) -> TokenStream {
	let CompactSolutionDef {
		vis,
		ident,
		count,
	} = syn::parse_macro_input!(item as CompactSolutionDef);

	let voter_type = GenericArgument::Type(Type::Verbatim(quote!(V)));
	let target_type = GenericArgument::Type(Type::Verbatim(quote!(T)));
	let weight_type = GenericArgument::Type(Type::Verbatim(quote!(W)));

	let imports = imports().unwrap_or_else(|e| e.to_compile_error());

	let compact_def = struct_def(
		vis,
		ident.clone(),
		count,
		voter_type.clone(),
		target_type.clone(),
		weight_type,
	).unwrap_or_else(|e| e.to_compile_error());

	let assignment_impls = assignment::assignment(
		ident.clone(),
		voter_type.clone(),
		target_type.clone(),
		count,
	);

	let staked_impls = staked::staked(
		ident,
		voter_type,
		target_type,
		count,
	);

	quote!(
		#imports
		#compact_def
		#assignment_impls
		#staked_impls
	).into()
}

fn struct_def(
	vis: syn::Visibility,
	ident: syn::Ident,
	count: usize,
	voter_type: GenericArgument,
	target_type: GenericArgument,
	weight_type: GenericArgument,
) -> Result<TokenStream2> {
	if count <= 2 {
		Err(syn::Error::new(
			Span::call_site(),
			"cannot build compact solution struct with capacity less than 2."
		))?
	}

	let singles = {
		let name = field_name_for(1);
		quote!(#name: Vec<(#voter_type, #target_type)>,)
	};

	let doubles = {
		let name = field_name_for(2);
		quote!(#name: Vec<(#voter_type, (#target_type, #weight_type), #target_type)>,)
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

	Ok(quote! (
		/// A struct to encode a election assignment in a compact way.
		#[derive(
			Default,
			PartialEq,
			Eq,
			Clone,
			Debug,
			_phragmen::codec::Encode,
			_phragmen::codec::Decode,
		)]
		#vis struct #ident<#voter_type, #target_type, #weight_type> {
			// _marker: sp_std::marker::PhantomData<A>,
			#singles
			#doubles
			#rest
		}

		impl<#voter_type, #target_type, #weight_type> _phragmen::VotingLimit
		for #ident<#voter_type, #target_type, #weight_type>
		{
			const LIMIT: usize = #count;
		}

		impl<#voter_type, #target_type, #weight_type> #ident<#voter_type, #target_type, #weight_type> {
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
			use crate as _phragmen;
		})
	} else {
		match crate_name("sp-npos-elections") {
			Ok(sp_npos_elections) => {
				let ident = syn::Ident::new(&sp_npos_elections, Span::call_site());
				Ok(quote!( extern crate #ident as _phragmen; ))
			},
			Err(e) => Err(syn::Error::new(Span::call_site(), &e)),
		}
	}
}

struct CompactSolutionDef {
	vis: syn::Visibility,
	ident: syn::Ident,
	count: usize,
}

impl Parse for CompactSolutionDef {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let vis: syn::Visibility = input.parse()?;
		let ident: syn::Ident = input.parse()?;
		let _ = <syn::Token![,]>::parse(input)?;
		let count_literal: syn::LitInt = input.parse()?;
		let count = count_literal.base10_parse::<usize>()?;
		Ok(Self { vis, ident, count } )
	}
}

fn field_name_for(n: usize) -> Ident {
	Ident::new(&format!("{}{}", PREFIX, n), Span::call_site())
}
