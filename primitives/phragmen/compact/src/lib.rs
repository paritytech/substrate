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

//! Proc macro for phragmen compact assignment.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Span, Ident};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::{GenericArgument, Type, parse::{Parse, ParseStream, Result}};

mod assignment;
mod staked;

// prefix used for struct fields in compact.
const PREFIX: &'static str = "votes";

/// Generates a struct to store the phragmen assignments in a compact way. The struct can only store
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

	Ok(quote! (
		/// A struct to encode a Phragmen assignment in a compact way.
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
	))
}

fn imports() -> Result<TokenStream2> {
	let sp_phragmen_imports = match crate_name("sp-phragmen") {
		Ok(sp_phragmen) => {
			let ident = syn::Ident::new(&sp_phragmen, Span::call_site());
			quote!( extern crate #ident as _phragmen; )
		}
		Err(e) => return Err(syn::Error::new(Span::call_site(), &e)),
	};

	Ok(quote!(
		#sp_phragmen_imports
	))
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
