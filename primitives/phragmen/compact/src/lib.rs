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

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Span, Ident};
use quote::quote;
use syn::parse::{Parse, ParseStream};

const PREFIX: &'static str = "votes";

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

/// Generates a struct to store the phragmen assignments in a compact way. The struct can only store
/// distributions up to the given input count. The given count must be greater than 2.
///
/// The generated structure creates one key for each possible count of distributions from 1 up to
/// the given length. A normal distribution is a tuple of `(candidate, weight)` where `candidate` is
/// a generic `AccountId` and `weight` is a `Perbill`. The following rules hold regarding the
/// compact representation:
///   - For single distribution, no weight is stored. The weight is known to be 100%.
///   - For all the rest, the weight if the last distribution is omitted. This value can be computed
///     from the rest.
#[proc_macro]
pub fn generate_compact_solution_type(item: TokenStream) -> TokenStream {
	let CompactSolutionDef {
		vis,
		ident,
		count,
	} = syn::parse_macro_input!(item as CompactSolutionDef);
	let account_type = quote!(AccountId);

	if count <= 2 {
		panic!("cannot build compact solution struct with capacity less than 2.");
	}

	let singles = {
		let name = field_name_for(1);
		quote!(#name: Vec<(#account_type, #account_type)>,)
	};
	let doubles = {
		let name = field_name_for(2);
		quote!(#name: Vec<(#account_type, (#account_type, Perbill), #account_type)>,)
	};
	let rest = (3..=count).map(|c| {
		let field_name = field_name_for(c);
		let array_len = c - 1;
		quote!(
			#field_name: Vec<(
				#account_type,
				[(#account_type, sp_runtime::Perbill); #array_len],
				#account_type
			)>,
		)
	}).collect::<TokenStream2>();

	let compact_def = quote! (
		// TODO: clean imports: how to deal with codec?
		#[derive(Default, PartialEq, Eq, Clone, sp_runtime::RuntimeDebug, codec::Encode, codec::Decode)]
		#vis struct #ident<#account_type> {
			#singles
			#doubles
			#rest
		}
	);

	let from_impl_single = {
		let name = field_name_for(1);
		quote!(1 => compact.#name.push((who, distribution[0].clone().0)),)
	};
	let from_impl_double = {
		let name = field_name_for(2);
		quote!(2 => compact.#name.push((who, distribution[0].clone(), distribution[1].clone().0)),)
	};
	let from_impl_rest = (3..=count).map(|c| {
		let inner = (0..c-1).map(|i| quote!(distribution[#i].clone(),)).collect::<TokenStream2>();

		let field_name = field_name_for(c);
		let last_index = c - 1;
		let last = quote!(distribution[#last_index].clone().0);

		quote!(
			#c => compact.#field_name.push((who, [#inner], #last)),
		)
	}).collect::<TokenStream2>();

	let from_impl = quote!(
		impl<#account_type: codec::Codec + Default + Clone>
		From<Vec<Assignment<#account_type>>>
		for #ident<#account_type>
		{
			fn from(
				assignments: Vec<Assignment<#account_type>>,
			) -> Self {
				let mut compact: #ident<#account_type> = Default::default();
				assignments.into_iter().for_each(|Assignment { who, distribution } | {
					match distribution.len() {
						#from_impl_single
						#from_impl_double
						#from_impl_rest
						_ => {
							sp_runtime::print("assignment length too big. ignoring");
						}
					}
				});
				compact
			}
		}
	);

	let into_impl_single = {
		let name = field_name_for(1);
		quote!(
			for (who, target) in self.#name {
				assignments.push(Assignment {
					who,
					distribution: vec![(target, Perbill::one())],
				})
			}
		)
	};
	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (who, (t1, p1), t2) in self.#name {
				let p2 = Perbill::one().saturating_sub(p1);
				assignments.push( Assignment {
					who,
					distribution: vec![
						(t1, p1),
						(t2, p2),
					]
				});
			}
		)
	};
	let into_impl_rest = (3..=count).map(|c| {
		let name = field_name_for(c);
		quote!(
			for (who, inners, t_last) in self.#name {
				let mut sum = Perbill::zero();
				let mut inners_parsed = inners
					.into_iter()
					.map(|(ref c, p)| {
						sum = sum.saturating_add(*p);
						(c.clone(), *p)
					}).collect::<Vec<(#account_type, Perbill)>>();

				let p_last = Perbill::one().saturating_sub(sum);
				inners_parsed.push((t_last, p_last));

				assignments.push(Assignment {
					who,
					distribution: inners_parsed,
				});
			}
		)
	}).collect::<TokenStream2>();

	let into_impl = quote!(
		impl<#account_type: codec::Codec + Default + Clone>
		Into<Vec<Assignment<#account_type>>>
		for #ident<#account_type>
		{
			fn into(self) -> Vec<Assignment<#account_type>> {
				let mut assignments: Vec<Assignment<AccountId>> = Default::default();
				#into_impl_single
				#into_impl_double
				#into_impl_rest

				assignments
			}
		}
	);

	quote!(
		#compact_def
		#from_impl
		#into_impl
	).into()
}
