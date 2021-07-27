// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use crate::{syn_err, vote_filed};
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::parse::Result;

pub(crate) fn generate(
	vis: syn::Visibility,
	ident: syn::Ident,
	count: usize,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
	compact_encoding: bool,
) -> Result<TokenStream2> {
	if count <= 2 {
		Err(syn_err("cannot build solution struct with capacity less than 3."))?
	}

	let singles = {
		let name = vote_filed(1);
		// NOTE: we use the visibility of the struct for the fields as well.. could be made better.
		quote!(
			#vis #name: _npos::sp_std::prelude::Vec<(#voter_type, #target_type)>,
		)
	};

	let doubles = {
		let name = vote_filed(2);
		quote!(
			#vis #name: _npos::sp_std::prelude::Vec<(#voter_type, (#target_type, #weight_type), #target_type)>,
		)
	};

	let rest = (3..=count)
		.map(|c| {
			let field_name = vote_filed(c);
			let array_len = c - 1;
			quote!(
				#vis #field_name: _npos::sp_std::prelude::Vec<(
					#voter_type,
					[(#target_type, #weight_type); #array_len],
					#target_type
				)>,
			)
		})
		.collect::<TokenStream2>();

	let len_impl = len_impl(count);
	let edge_count_impl = edge_count_impl(count);
	let unique_targets_impl = unique_targets_impl(count);
	let remove_voter_impl = remove_voter_impl(count);

	let derives_and_maybe_compact_encoding = if compact_encoding {
		// custom compact encoding.
		let compact_impl = crate::codec::codec_impl(
			ident.clone(),
			voter_type.clone(),
			target_type.clone(),
			weight_type.clone(),
			count,
		);
		quote! {
			#compact_impl
			#[derive(Default, PartialEq, Eq, Clone, Debug, PartialOrd, Ord)]
		}
	} else {
		// automatically derived.
		quote!(#[derive(Default, PartialEq, Eq, Clone, Debug, _npos::codec::Encode, _npos::codec::Decode)])
	};

	let struct_name = syn::Ident::new("solution", proc_macro2::Span::call_site());
	let assignment_name = syn::Ident::new("all_assignments", proc_macro2::Span::call_site());

	let from_impl = crate::assignment::from_impl_single_page(&struct_name, count);
	let into_impl =
		crate::assignment::into_impl_single_page(&assignment_name, count, weight_type.clone());
	let from_index_impl = crate::index_assignment::from_impl(&struct_name, count);

	Ok(quote! (
		/// A struct to encode a election assignment in a compact way.
		#derives_and_maybe_compact_encoding
		#vis struct #ident { #singles #doubles #rest }

		use _npos::__OrInvalidIndex;
		impl _npos::SolutionBase for #ident {
			const LIMIT: usize = #count;
			type Voter = #voter_type;
			type Target = #target_type;
			type Accuracy = #weight_type;

			fn voter_count(&self) -> usize {
				let mut all_len = 0usize;
				#len_impl
				all_len
			}

			fn edge_count(&self) -> usize {
				let mut all_edges = 0usize;
				#edge_count_impl
				all_edges
			}

			fn unique_targets(&self) -> _npos::sp_std::prelude::Vec<Self::Target> {
				// NOTE: this implementation returns the targets sorted, but we don't use it yet per
				// se, nor is the API enforcing it.
				use _npos::sp_std::collections::btree_set::BTreeSet;
				let mut all_targets: BTreeSet<Self::Target> = BTreeSet::new();
				let mut maybe_insert_target = |t: Self::Target| {
					all_targets.insert(t);
				};

				#unique_targets_impl

				all_targets.into_iter().collect()
			}
		}

		impl _npos::Solution for #ident {
			fn remove_voter(&mut self, to_remove: Self::Voter) -> bool {
				#remove_voter_impl
				return false
			}

			fn from_assignment<FV, FT, A>(
				assignments: &[_npos::Assignment<A, #weight_type>],
				voter_index: FV,
				target_index: FT,
			) -> Result<Self, _npos::Error>
				where
					A: _npos::IdentifierT,
					for<'r> FV: Fn(&'r A) -> Option<Self::Voter>,
					for<'r> FT: Fn(&'r A) -> Option<Self::Target>,
			{
				let mut #struct_name: #ident = Default::default();
				for _npos::Assignment { who, distribution } in assignments {
					match distribution.len() {
						0 => continue,
						#from_impl
						_ => {
							return Err(_npos::Error::SolutionTargetOverflow);
						}
					}
				};
				Ok(#struct_name)
			}

			fn into_assignment<A: _npos::IdentifierT>(
				self,
				voter_at: impl Fn(Self::Voter) -> Option<A>,
				target_at: impl Fn(Self::Target) -> Option<A>,
			) -> Result<_npos::sp_std::prelude::Vec<_npos::Assignment<A, #weight_type>>, _npos::Error> {
				let mut #assignment_name: _npos::sp_std::prelude::Vec<_npos::Assignment<A, #weight_type>> = Default::default();
				#into_impl
				Ok(#assignment_name)
			}
		}

		type __IndexAssignment = _npos::IndexAssignment<
			<#ident as _npos::SolutionBase>::Voter,
			<#ident as _npos::SolutionBase>::Target,
			<#ident as _npos::SolutionBase>::Accuracy,
		>;
		impl<'a> _npos::sp_std::convert::TryFrom<&'a [__IndexAssignment]> for #ident {
			type Error = _npos::Error;
			fn try_from(index_assignments: &'a [__IndexAssignment]) -> Result<Self, Self::Error> {
				let mut #struct_name =  #ident::default();

				for _npos::IndexAssignment { who, distribution } in index_assignments {
					match distribution.len() {
						0 => {}
						#from_index_impl
						_ => {
							return Err(_npos::Error::SolutionTargetOverflow);
						}
					}
				};

				Ok(#struct_name)
			}
		}
	))
}

fn remove_voter_impl(count: usize) -> TokenStream2 {
	let field_name = vote_filed(1);
	let single = quote! {
		if let Some(idx) = self.#field_name.iter().position(|(x, _)| *x == to_remove) {
			self.#field_name.remove(idx);
			return true
		}
	};

	let field_name = vote_filed(2);
	let double = quote! {
		if let Some(idx) = self.#field_name.iter().position(|(x, _, _)| *x == to_remove) {
			self.#field_name.remove(idx);
			return true
		}
	};

	let rest = (3..=count)
		.map(|c| {
			let field_name = vote_filed(c);
			quote! {
				if let Some(idx) = self.#field_name.iter().position(|(x, _, _)| *x == to_remove) {
					self.#field_name.remove(idx);
					return true
				}
			}
		})
		.collect::<TokenStream2>();

	quote! {
		#single
		#double
		#rest
	}
}

fn len_impl(count: usize) -> TokenStream2 {
	(1..=count)
		.map(|c| {
			let field_name = vote_filed(c);
			quote!(
				all_len = all_len.saturating_add(self.#field_name.len());
			)
		})
		.collect::<TokenStream2>()
}

fn edge_count_impl(count: usize) -> TokenStream2 {
	(1..=count)
		.map(|c| {
			let field_name = vote_filed(c);
			quote!(
				all_edges = all_edges.saturating_add(
					self.#field_name.len().saturating_mul(#c as usize)
				);
			)
		})
		.collect::<TokenStream2>()
}

fn unique_targets_impl(count: usize) -> TokenStream2 {
	let unique_targets_impl_single = {
		let field_name = vote_filed(1);
		quote! {
			self.#field_name.iter().for_each(|(_, t)| {
				maybe_insert_target(*t);
			});
		}
	};

	let unique_targets_impl_double = {
		let field_name = vote_filed(2);
		quote! {
			self.#field_name.iter().for_each(|(_, (t1, _), t2)| {
				maybe_insert_target(*t1);
				maybe_insert_target(*t2);
			});
		}
	};

	let unique_targets_impl_rest = (3..=count)
		.map(|c| {
			let field_name = vote_filed(c);
			quote! {
				self.#field_name.iter().for_each(|(_, inners, t_last)| {
					inners.iter().for_each(|(t, _)| {
						maybe_insert_target(*t);
					});
					maybe_insert_target(*t_last);
				});
			}
		})
		.collect::<TokenStream2>();

	quote! {
		#unique_targets_impl_single
		#unique_targets_impl_double
		#unique_targets_impl_rest
	}
}
