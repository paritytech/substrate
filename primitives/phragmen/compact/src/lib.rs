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
/// 3 generic types must be given to the type
///
/// - `V`: identifier/index type of the voter.
/// - `T`: identifier/index type of the target.
/// - `W`: any type used as the edge weight.
///
/// ```rust
/// // generate a struct with nominator and edge weight u128, with maximum supported
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
/// struct TestCompact<V, T, W> {
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

	let from_into_impl_assignment = convert_impl_for_assignment(
		ident.clone(),
		voter_type.clone(),
		target_type.clone(),
		count,
	);

	let from_into_impl_staked_assignment = convert_impl_for_staked_assignment(
		ident,
		voter_type,
		target_type,
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
		/// A struct to encode a `Vec<StakedAssignment>` or `Vec<Assignment>` of the phragmen module
		/// in a compact way.
		#[derive(Default, PartialEq, Eq, Clone, _sp_runtime::RuntimeDebug, _codec::Encode, _codec::Decode)]
		#vis struct #ident<#voter_type, #target_type, #weight_type, A> {
			_marker: sp_std::marker::PhantomData<A>,
			#singles
			#doubles
			#rest
		}
	))
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
	voter_type: GenericArgument,
	target_type: GenericArgument,
	count: usize
) -> TokenStream2 {
	let from_impl_single = {
		let name = field_name_for(1);
		quote!(1 => compact.#name.push(
			(
				index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?,
				index_of_target(&distribution[0].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
			)
		),)
	};
	let from_impl_double = {
		let name = field_name_for(2);
		quote!(2 => compact.#name.push(
			(
				index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?,
				(
					index_of_target(&distribution[0].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution[0].1,
				),
				index_of_target(&distribution[1].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
			)
		),)
	};
	let from_impl_rest = (3..=count).map(|c| {
		let inner = (0..c-1).map(|i|
			quote!((index_of_target(&distribution[#i].0).ok_or(_phragmen::Error::CompactInvalidIndex)?, distribution[#i].1),)
		).collect::<TokenStream2>();

		let field_name = field_name_for(c);
		let last_index = c - 1;
		let last = quote!(index_of_target(&distribution[#last_index].0).ok_or(_phragmen::Error::CompactInvalidIndex)?);

		quote!(
			#c => compact.#field_name.push((index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?, [#inner], #last)),
		)
	}).collect::<TokenStream2>();

	let into_impl_single = {
		let name = field_name_for(1);
		quote!(
			for (voter_index, target_index) in self.#name {
				assignments.push(_phragmen::Assignment {
					who: voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution: vec![
						(target_at(target_index).ok_or(_phragmen::Error::CompactInvalidIndex)?, _sp_runtime::Perbill::one())
					],
				})
			}
		)
	};
	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (voter_index, (t1_idx, p1), t2_idx) in self.#name {
				if p1 >= _sp_runtime::Perbill::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// defensive only. Since perbill doesn't have `Sub`.
				let p2 = _sp_runtime::traits::Saturating::saturating_sub(
					_sp_runtime::Perbill::one(),
					p1,
				);

				assignments.push( _phragmen::Assignment {
					who: voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution: vec![
						(target_at(t1_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, p1),
						(target_at(t2_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, p2),
					]
				});
			}
		)
	};
	let into_impl_rest = (3..=count).map(|c| {
		let name = field_name_for(c);
		quote!(
			for (voter_index, inners, t_last_idx) in self.#name {
				let mut sum = _sp_runtime::Perbill::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _sp_runtime::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, _sp_runtime::Perbill)>, _phragmen::Error>>()?;

				if sum >= _sp_runtime::Perbill::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// defensive only. Since perbill doesn't have `Sub`.
				let p_last = _sp_runtime::traits::Saturating::saturating_sub(
					_sp_runtime::Perbill::one(),
					sum,
				);

				inners_parsed.push((target_at(t_last_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, p_last));

				assignments.push(_phragmen::Assignment {
					who: voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution: inners_parsed,
				});
			}
		)
	}).collect::<TokenStream2>();

	let from_into_impl = quote!(
		impl<
			#voter_type: _codec::Codec + Default + Copy,
			#target_type: _codec::Codec + Default + Copy,
			A: _codec::Codec + Default + Clone,
		>
		#ident<#voter_type, #target_type, _sp_runtime::Perbill, A>
		{
			pub fn from_assignment<FV, FT>(
				assignments: Vec<_phragmen::Assignment<A>>,
				index_of_voter: FV,
				index_of_target: FT,
			) -> Result<Self, _phragmen::Error>
				where
					for<'r> FV: Fn(&'r A) -> Option<#voter_type>,
					for<'r> FT: Fn(&'r A) -> Option<#target_type>,
			{
				let mut compact: #ident<
					#voter_type,
					#target_type,
					_sp_runtime::Perbill,
					A,
				> = Default::default();

				for _phragmen::Assignment { who, distribution } in assignments {
					match distribution.len() {
						#from_impl_single
						#from_impl_double
						#from_impl_rest
						_ => {
							return Err(_phragmen::Error::CompactTargetOverflow);
						}
					}
				};
				Ok(compact)
			}

			pub fn into_assignment(
				self,
				voter_at: impl Fn(#voter_type) -> Option<A>,
				target_at: impl Fn(#target_type) -> Option<A>,
			) -> Result<Vec<_phragmen::Assignment<A>>, _phragmen::Error> {
				let mut assignments: Vec<_phragmen::Assignment<A>> = Default::default();
				#into_impl_single
				#into_impl_double
				#into_impl_rest

				Ok(assignments)
			}
		}
	);

	from_into_impl
}

fn convert_impl_for_staked_assignment(
	ident: syn::Ident,
	voter_type: GenericArgument,
	target_type: GenericArgument,
	count: usize,
) -> TokenStream2 {
	let from_impl_single = {
		let name = field_name_for(1);
		quote!(1 => compact.#name.push(
			(
				index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?,
				index_of_target(&distribution[0].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
			)
		),)
	};
	let from_impl_double = {
		let name = field_name_for(2);
		quote!(2 => compact.#name.push(
			(
				index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?,
				(
					index_of_target(&distribution[0].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution[0].1,
				),
				index_of_target(&distribution[1].0).ok_or(_phragmen::Error::CompactInvalidIndex)?,
			)
		),)
	};
	let from_impl_rest = (3..=count).map(|c| {
		let inner = (0..c-1).map(|i|
			quote!((index_of_target(&distribution[#i].0).ok_or(_phragmen::Error::CompactInvalidIndex)?, distribution[#i].1),)
		).collect::<TokenStream2>();

		let field_name = field_name_for(c);
		let last_index = c - 1;
		let last = quote!(index_of_target(&distribution[#last_index].0).ok_or(_phragmen::Error::CompactInvalidIndex)?);

		quote!(
			#c => compact.#field_name.push((index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?, [#inner], #last)),
		)
	}).collect::<TokenStream2>();

	let into_impl_single = {
		let name = field_name_for(1);
		quote!(
			for (voter_index, target_index) in self.#name {
				let who = voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?;
				let all_stake = max_of(&who);
				assignments.push(_phragmen::StakedAssignment {
					who,
					distribution: vec![(target_at(target_index).ok_or(_phragmen::Error::CompactInvalidIndex)?, all_stake)],
				})
			}
		)
	};
	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (voter_index, (t1_idx, w1), t2_idx) in self.#name {
				let who = voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?;
				let all_stake = max_of(&who);

				if w1 >= all_stake {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// w2 is ensured to be positive.
				let w2 = all_stake - w1;
				assignments.push( _phragmen::StakedAssignment {
					who,
					distribution: vec![
						(target_at(t1_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, w1),
						(target_at(t2_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, w2),
					]
				});
			}
		)
	};
	let into_impl_rest = (3..=count).map(|c| {
		let name = field_name_for(c);
		quote!(
			for (voter_index, inners, t_last_idx) in self.#name {
				let who = voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?;
				let mut sum = u128::min_value();
				let all_stake = max_of(&who);

				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, w)| {
						sum = sum.saturating_add(*w);
						let target = target_at(*t_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?;
						Ok((target, *w))
					}).collect::<Result<Vec<(A, u128)>, _phragmen::Error>>()?;

				if sum >= all_stake {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}
				// w_last is proved to be positive.
				let w_last = all_stake - sum;

				inners_parsed.push((target_at(t_last_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?, w_last));

				assignments.push(_phragmen::StakedAssignment {
					who,
					distribution: inners_parsed,
				});
			}
		)
	}).collect::<TokenStream2>();

	let final_impl = quote!(
		impl<
			#voter_type: _codec::Codec + Default + Copy,
			#target_type: _codec::Codec + Default + Copy,
			A: _codec::Codec + Default + Clone,
		>
		#ident<#voter_type, #target_type, u128, A>
		{
			/// Convert self into `StakedAssignment`. The given function should return the total
			/// weight of a voter. It is used to subtract the sum of all the encoded weights to
			/// infer the last one.
			pub fn into_staked<FM>(
				self,
				max_of: FM,
				voter_at: impl Fn(#voter_type) -> Option<A>,
				target_at: impl Fn(#target_type) -> Option<A>,
			)
				-> Result<Vec<_phragmen::StakedAssignment<A>>, _phragmen::Error>
			where
				for<'r> FM: Fn(&'r A) -> u128,
			{
				let mut assignments: Vec<_phragmen::StakedAssignment<A>> = Default::default();
				#into_impl_single
				#into_impl_double
				#into_impl_rest

				Ok(assignments)
			}

			/// Generate self from a vector of `StakedAssignment`.
			pub fn from_staked<FV, FT>(
				assignments: Vec<_phragmen::StakedAssignment<A>>,
				index_of_voter: FV,
				index_of_target: FT,
			) -> Result<Self, _phragmen::Error>
				where
					for<'r> FV: Fn(&'r A) -> Option<#voter_type>,
					for<'r> FT: Fn(&'r A) -> Option<#target_type>,
			{
				let mut compact: #ident<#voter_type, #target_type, u128, A> = Default::default();
				for _phragmen::StakedAssignment { who, distribution }  in assignments {
					match distribution.len() {
						#from_impl_single
						#from_impl_double
						#from_impl_rest
						_ => {
							return Err(_phragmen::Error::CompactTargetOverflow);
						}
					}
				};
				Ok(compact)
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
