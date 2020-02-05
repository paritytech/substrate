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
use proc_macro_crate::crate_name;
use quote::quote;
use syn::{GenericArgument, Type, parse::{Parse, ParseStream, Result}};

// prefix used for struct fields in compact.
const PREFIX: &'static str = "votes";

// TODO: what to do if additions overflow in into staked.

/// Generates a struct to store the phragmen assignments in a compact way. The struct can only store
/// distributions up to the given input count. The given count must be greater than 2.
///
/// ```rust
/// // generate a struct with account Identifier u32 and edge weight u128, with maximum supported
/// // edge per voter of 32.
/// generate_compact_solution_type(TestCompact<u32, u128>, 32)
/// ```
///
/// The generated structure creates one key for each possible count of distributions from 1 up to
/// the given length. A normal distribution is a tuple of `(candidate, weight)`. Typically, the
/// weight can refer to either the ratio of the voter's support or its absolute value. The following
/// rules hold regarding the compact representation:
///   - For single distribution, no weight is stored. The weight is known to be 100%.
///   - For all the rest, the weight if the last distribution is omitted. This value can be computed
///     from the rest.
///
/// An example expansion of length 16 is as follows:
///
/// ```rust
/// struct TestCompact<AccountId, W> {
/// 	votes1: Vec<(AccountId, AccountId)>,
/// 	votes2: Vec<(AccountId, (AccountId, W), AccountId)>,
/// 	votes3: Vec<(AccountId, [(AccountId, W); 2usize], AccountId)>,
/// 	votes4: Vec<(AccountId, [(AccountId, W); 3usize], AccountId)>,
/// 	votes5: Vec<(AccountId, [(AccountId, W); 4usize], AccountId)>,
/// 	votes6: Vec<(AccountId, [(AccountId, W); 5usize], AccountId)>,
/// 	votes7: Vec<(AccountId, [(AccountId, W); 6usize], AccountId)>,
/// 	votes8: Vec<(AccountId, [(AccountId, W); 7usize], AccountId)>,
/// 	votes9: Vec<(AccountId, [(AccountId, W); 8usize], AccountId)>,
/// 	votes10: Vec<(AccountId, [(AccountId, W); 9usize], AccountId)>,
/// 	votes11: Vec<(AccountId, [(AccountId, W); 10usize], AccountId)>,
/// 	votes12: Vec<(AccountId, [(AccountId, W); 11usize], AccountId)>,
/// 	votes13: Vec<(AccountId, [(AccountId, W); 12usize], AccountId)>,
/// 	votes14: Vec<(AccountId, [(AccountId, W); 13usize], AccountId)>,
/// 	votes15: Vec<(AccountId, [(AccountId, W); 14usize], AccountId)>,
/// 	votes16: Vec<(AccountId, [(AccountId, W); 15usize], AccountId)>,
/// }
/// ```
#[proc_macro]
pub fn generate_compact_solution_type(item: TokenStream) -> TokenStream {
	let CompactSolutionDef {
		vis,
		ident,
		count,
	} = syn::parse_macro_input!(item as CompactSolutionDef);

	let account_type = GenericArgument::Type(Type::Verbatim(quote!(AccountId)));
	let weight_type = GenericArgument::Type(Type::Verbatim(quote!(weight)));

	let imports = imports().unwrap_or_else(|e| e.to_compile_error());

	let compact_def = struct_def(
		vis,
		ident.clone(),
		count,
		account_type.clone(),
		weight_type,
	).unwrap_or_else(|e| e.to_compile_error());

	let from_into_impl_assignment = convert_impl_for_assignment(
		ident.clone(),
		account_type.clone(),
		count,
	);

	let from_into_impl_staked_assignment = convert_impl_for_staked_assignment(
		ident,
		account_type,
		count,
	);

	quote!(
		#imports
		#compact_def
		#from_into_impl_assignment
		#from_into_impl_staked_assignment
	).into()
}

fn struct_def(
	vis: syn::Visibility,
	ident: syn::Ident,
	count: usize,
	account_type: GenericArgument,
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
		quote!(#name: Vec<(#account_type, #account_type)>,)
	};

	let doubles = {
		let name = field_name_for(2);
		quote!(#name: Vec<(#account_type, (#account_type, #weight_type), #account_type)>,)
	};

	let rest = (3..=count).map(|c| {
		let field_name = field_name_for(c);
		let array_len = c - 1;
		quote!(
			#field_name: Vec<(
				#account_type,
				[(#account_type, #weight_type); #array_len],
				#account_type
			)>,
		)
	}).collect::<TokenStream2>();

	let compact_def = quote! (
		/// A struct to encode a `Vec<StakedAssignment>` or `Vec<_phragmen::Assignment>` of the phragmen module
		/// in a compact way.
		#[derive(Default, PartialEq, Eq, Clone, _sp_runtime::RuntimeDebug, _codec::Encode, _codec::Decode)]
		#vis struct #ident<#account_type, #weight_type> {
			#singles
			#doubles
			#rest
		}
	);

	Ok(compact_def)
}

fn imports() -> Result<TokenStream2> {
	let runtime_imports = match crate_name("sp-runtime") {
		Ok(sp_runtime) => {
			let ident = syn::Ident::new(&sp_runtime, Span::call_site());
			quote!( extern crate #ident as _sp_runtime; )
		},
		Err(e) => return Err(syn::Error::new(Span::call_site(), &e)),
	};
	let codec_imports = match crate_name("parity-scale-codec") {
		Ok(codec) => {
			let ident = syn::Ident::new(&codec, Span::call_site());
			quote!( extern crate #ident as _codec; )
		},
		Err(e) => return Err(syn::Error::new(Span::call_site(), &e)),
	};
	let sp_phragmen_imports = match crate_name("sp-phragmen") {
		Ok(sp_phragmen) => {
			let ident = syn::Ident::new(&sp_phragmen, Span::call_site());
			quote!( extern crate #ident as _phragmen; )
		}
		Err(e) => return Err(syn::Error::new(Span::call_site(), &e)),
	};
	let sp_std_imports = match crate_name("sp-std") {
		Ok(sp_std) => {
			let ident = syn::Ident::new(&sp_std, Span::call_site());
			quote!( extern crate #ident as _sp_std; )
		}
		Err(e) => return Err(syn::Error::new(Span::call_site(), &e)),
	};

	Ok(quote!(
		#runtime_imports
		#codec_imports
		#sp_phragmen_imports
		#sp_std_imports
	))
}

fn convert_impl_for_assignment(
	ident: syn::Ident,
	account_type: GenericArgument,
	count: usize
) -> TokenStream2 {
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
		impl<#account_type: _codec::Codec + Default + Clone>
		From<Vec<_phragmen::Assignment<#account_type>>>
		for #ident<#account_type, _sp_runtime::Perbill>
		{
			fn from(
				assignments: Vec<_phragmen::Assignment<#account_type>>,
			) -> Self {
				let mut compact: #ident<#account_type, _sp_runtime::Perbill> = Default::default();
				assignments.into_iter().for_each(|_phragmen::Assignment { who, distribution } | {
					match distribution.len() {
						#from_impl_single
						#from_impl_double
						#from_impl_rest
						_ => {
							_sp_runtime::print("assignment length too big. ignoring");
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
				assignments.push(_phragmen::Assignment {
					who,
					distribution: vec![(target, _sp_runtime::Perbill::one())],
				})
			}
		)
	};
	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (who, (t1, p1), t2) in self.#name {
				if p1 >= _sp_runtime::Perbill::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}
				// defensive only. Since perbill doesn't have `Sub`.
				let p2 = _sp_runtime::traits::Saturating::saturating_sub(_sp_runtime::Perbill::one(), p1);
				assignments.push( _phragmen::Assignment {
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
				let mut sum = _sp_runtime::Perbill::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref c, p)| {
						sum = _sp_runtime::traits::Saturating::saturating_add(sum, *p);
						(c.clone(), *p)
					}).collect::<Vec<(#account_type, _sp_runtime::Perbill)>>();

				if sum >= _sp_runtime::Perbill::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}
				// defensive only. Since perbill doesn't have `Sub`.
				let p_last = _sp_runtime::traits::Saturating::saturating_sub(_sp_runtime::Perbill::one(), sum);
				inners_parsed.push((t_last, p_last));

				assignments.push(_phragmen::Assignment {
					who,
					distribution: inners_parsed,
				});
			}
		)
	}).collect::<TokenStream2>();

	let into_impl = quote!(
		impl<#account_type: _codec::Codec + Default + Clone>
		_sp_std::convert::TryInto<Vec<_phragmen::Assignment<#account_type>>>
		for #ident<#account_type, _sp_runtime::Perbill>
		{
			type Error = _phragmen::Error;

			fn try_into(self) -> Result<Vec<_phragmen::Assignment<#account_type>>, Self::Error> {
				let mut assignments: Vec<_phragmen::Assignment<#account_type>> = Default::default();
				#into_impl_single
				#into_impl_double
				#into_impl_rest

				Ok(assignments)
			}
		}
	);

	quote!(
		#from_impl
		#into_impl
	)
}

fn convert_impl_for_staked_assignment(
	ident: syn::Ident,
	account_type: GenericArgument,
	count: usize
) -> TokenStream2 {
	let from_impl_single = {
		let name = field_name_for(1);
		quote!(1 => compact.#name.push((who, distribution[0].clone().0)),)
	};
	let from_impl_double = {
		let name = field_name_for(2);
		quote!(2 => compact.#name.push(
			(
				who,
				distribution[0].clone(),
				distribution[1].clone().0,
			)
		),)
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

	let into_impl_single = {
		let name = field_name_for(1);
		quote!(
			for (who, target) in self.#name {
				let all_stake = C::convert(max_of(&who)) as u128;
				assignments.push(_phragmen::StakedAssignment {
					who,
					distribution: vec![(target, all_stake)],
				})
			}
		)
	};
	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (who, (t1, w1), t2) in self.#name {
				let all_stake = C::convert(max_of(&who)) as u128;

				if w1 >= all_stake {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// w2 is ensured to be positive.
				let w2 = all_stake - w1;
				assignments.push( _phragmen::StakedAssignment {
					who,
					distribution: vec![
						(t1, w1),
						(t2, w2),
					]
				});
			}
		)
	};
	let into_impl_rest = (3..=count).map(|c| {
		let name = field_name_for(c);
		quote!(
			for (who, inners, t_last) in self.#name {
				let mut sum = u128::min_value();
				let all_stake = C::convert(max_of(&who)) as u128;
				let mut inners_parsed = inners
					.iter()
					.map(|(ref c, w)| {
						sum = sum.saturating_add(*w);
						(c.clone(), *w)
					}).collect::<Vec<(#account_type, u128)>>();

				if sum >= all_stake {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}
				// w_last is proved to be positive.
				let w_last = all_stake - sum;

				inners_parsed.push((t_last, w_last));

				assignments.push(_phragmen::StakedAssignment {
					who,
					distribution: inners_parsed,
				});
			}
		)
	}).collect::<TokenStream2>();

	let final_impl = quote!(
		impl<#account_type: _codec::Codec + Default + Clone>
		#ident<#account_type, u128>
		{
			/// Convert self into `StakedAssignment`. The given function should return the total
			/// weight of a voter. It is used to subtract the sum of all the encoded weights to
			/// infer the last one.
			fn into_staked<Balance, FM, C>(self, max_of: FM)
				-> Result<Vec<_phragmen::StakedAssignment<#account_type>>, _phragmen::Error>
			where
				for<'r> FM: Fn(&'r #account_type) -> Balance,
				C: _sp_runtime::traits::Convert<Balance, u64>
			{
				let mut assignments: Vec<_phragmen::StakedAssignment<#account_type>> = Default::default();
				#into_impl_single
				#into_impl_double
				#into_impl_rest

				Ok(assignments)
			}

			/// Generate self from a vector of `StakedAssignment`.
			fn from_staked(assignments: Vec<_phragmen::StakedAssignment<#account_type>>) -> Self {
				let mut compact: #ident<#account_type, u128> = Default::default();
				assignments.into_iter().for_each(|_phragmen::StakedAssignment { who, distribution } | {
					match distribution.len() {
						#from_impl_single
						#from_impl_double
						#from_impl_rest
						_ => {
							_sp_runtime::print("staked assignment length too big. ignoring");
						}
					}
				});
				compact
			}
		}
	);

	quote!(
		#final_impl
	)
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
