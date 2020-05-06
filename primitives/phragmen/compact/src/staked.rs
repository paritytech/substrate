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

//! Code generation for the staked assignment type.

use crate::field_name_for;
use proc_macro2::{TokenStream as TokenStream2};
use syn::{GenericArgument};
use quote::quote;

fn from_impl(count: usize) -> TokenStream2 {
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

	quote!(
		#from_impl_single
		#from_impl_double
		#from_impl_rest
	)
}

fn into_impl(count: usize) -> TokenStream2 {
	let into_impl_single = {
		let name = field_name_for(1);
		quote!(
			for (voter_index, target_index) in self.#name {
				let who = voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?;
				let all_stake: u128 = max_of(&who).into();
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
				let all_stake: u128 = max_of(&who).into();

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
				let all_stake: u128 = max_of(&who).into();

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

	quote!(
		#into_impl_single
		#into_impl_double
		#into_impl_rest
	)
}

pub(crate) fn staked(
	ident: syn::Ident,
	voter_type: GenericArgument,
	target_type: GenericArgument,
	count: usize,
) -> TokenStream2 {

	let from_impl = from_impl(count);
	let into_impl = into_impl(count);

	quote!(
		impl<
			#voter_type: _phragmen::codec::Codec + Default + Copy,
			#target_type: _phragmen::codec::Codec + Default + Copy,
		>
		#ident<#voter_type, #target_type, u128>
		{
			/// Generate self from a vector of `StakedAssignment`.
			pub fn from_staked<FV, FT, A>(
				assignments: Vec<_phragmen::StakedAssignment<A>>,
				index_of_voter: FV,
				index_of_target: FT,
			) -> Result<Self, _phragmen::Error>
				where
					for<'r> FV: Fn(&'r A) -> Option<#voter_type>,
					for<'r> FT: Fn(&'r A) -> Option<#target_type>,
					A: _phragmen::IdentifierT
			{
				let mut compact: #ident<#voter_type, #target_type, u128> = Default::default();
				for _phragmen::StakedAssignment { who, distribution }  in assignments {
					match distribution.len() {
						0 => continue,
						#from_impl
						_ => {
							return Err(_phragmen::Error::CompactTargetOverflow);
						}
					}
				};
				Ok(compact)
			}

			/// Convert self into `StakedAssignment`. The given function should return the total
			/// weight of a voter. It is used to subtract the sum of all the encoded weights to
			/// infer the last one.
			pub fn into_staked<FM, A>(
				self,
				max_of: FM,
				voter_at: impl Fn(#voter_type) -> Option<A>,
				target_at: impl Fn(#target_type) -> Option<A>,
			)
				-> Result<Vec<_phragmen::StakedAssignment<A>>, _phragmen::Error>
			where
				for<'r> FM: Fn(&'r A) -> u64,
				A: _phragmen::IdentifierT,
			{
				let mut assignments: Vec<_phragmen::StakedAssignment<A>> = Default::default();
				#into_impl
				Ok(assignments)
			}
		}
	)
}
