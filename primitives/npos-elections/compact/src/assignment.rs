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

//! Code generation for the ratio assignment type.

use crate::field_name_for;
use proc_macro2::TokenStream as TokenStream2;
use syn::GenericArgument;
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
			#c => compact.#field_name.push(
				(
					index_of_voter(&who).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					[#inner],
					#last,
				)
			),
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
				assignments.push(_phragmen::Assignment {
					who: voter_at(voter_index).ok_or(_phragmen::Error::CompactInvalidIndex)?,
					distribution: vec![
						(target_at(target_index).ok_or(_phragmen::Error::CompactInvalidIndex)?, Accuracy::one())
					],
				})
			}
		)
	};

	let into_impl_double = {
		let name = field_name_for(2);
		quote!(
			for (voter_index, (t1_idx, p1), t2_idx) in self.#name {
				if p1 >= Accuracy::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// defensive only. Since Percent doesn't have `Sub`.
				let p2 = _phragmen::sp_arithmetic::traits::Saturating::saturating_sub(
					Accuracy::one(),
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
				let mut sum = Accuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _phragmen::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).ok_or(_phragmen::Error::CompactInvalidIndex)?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, Accuracy)>, _phragmen::Error>>()?;

				if sum >= Accuracy::one() {
					return Err(_phragmen::Error::CompactStakeOverflow);
				}

				// defensive only. Since Percent doesn't have `Sub`.
				let p_last = _phragmen::sp_arithmetic::traits::Saturating::saturating_sub(
					Accuracy::one(),
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

	quote!(
		#into_impl_single
		#into_impl_double
		#into_impl_rest
	)
}

pub(crate) fn assignment(
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
			Accuracy:
				_phragmen::codec::Codec + Default + Clone + _phragmen::sp_arithmetic::PerThing +
				PartialOrd,
		>
		#ident<#voter_type, #target_type, Accuracy>
		{
			pub fn from_assignment<FV, FT, A>(
				assignments: Vec<_phragmen::Assignment<A, Accuracy>>,
				index_of_voter: FV,
				index_of_target: FT,
			) -> Result<Self, _phragmen::Error>
				where
					for<'r> FV: Fn(&'r A) -> Option<#voter_type>,
					for<'r> FT: Fn(&'r A) -> Option<#target_type>,
					A: _phragmen::IdentifierT,
			{
				let mut compact: #ident<
					#voter_type,
					#target_type,
					Accuracy,
				> = Default::default();

				for _phragmen::Assignment { who, distribution } in assignments {
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

			pub fn into_assignment<A: _phragmen::IdentifierT>(
				self,
				voter_at: impl Fn(#voter_type) -> Option<A>,
				target_at: impl Fn(#target_type) -> Option<A>,
			) -> Result<Vec<_phragmen::Assignment<A, Accuracy>>, _phragmen::Error> {
				let mut assignments: Vec<_phragmen::Assignment<A, Accuracy>> = Default::default();
				#into_impl
				Ok(assignments)
			}
		}
	)
}
