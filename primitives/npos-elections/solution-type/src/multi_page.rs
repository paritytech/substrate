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

use crate::{page_field, vote_filed, from_assignment_helpers::*};
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::parse::Result;

pub(crate) fn generate(
	vis: syn::Visibility,
	ident: syn::Ident,
	single_page_ident: syn::Ident,
	count: usize,
	voter_pages: u8,
	voter_type: syn::Type,
	target_type: syn::Type,
	weight_type: syn::Type,
) -> Result<TokenStream2> {
	let struct_name = syn::Ident::new("solution", proc_macro2::Span::call_site());

	let paged_fields = (0..voter_pages)
		.map(|i| {
			let name = page_field(i);
			quote!(#name: #single_page_ident,)
		})
		.collect::<TokenStream2>();

	let voter_count_impl = {
		let per_page = (0..voter_pages).map(|i| {
			let filed = page_field(i);
			quote!(sum = sum.saturating_add(self.#filed.voter_count());)
		});

		quote!(
			let mut sum = 0usize;
			#( #per_page )*
			sum
		)
	};

	let edge_count_impl = {
		let per_page = (0..voter_pages).map(|i| {
			let filed = page_field(i);
			quote!(sum = sum.saturating_add(self.#filed.edge_count());)
		});

		quote!(
			let mut sum = 0usize;
			#( #per_page )*
			sum
		)
	};

	let unique_targets_impl = {
		let per_page = (0..voter_pages).map(|i| {
			let filed = page_field(i);
			quote!(all_targets.extend(self.#filed.unique_targets());)
		});

		quote!(
			let mut all_targets: Vec<Self::Target> = Vec::new();
			#( #per_page )*
			all_targets.sort();
			all_targets.dedup();
			all_targets
		)
	};

	let remove_voter_impl_per_page = {
		(0..voter_pages).map(|i| {
			let filed = page_field(i);
			quote!(#i => self.#filed.remove_voter(to_remove),)
		})
	};

	let from_impl_per_page = {
		// TODO: voter_pages must always be bigger than 2.x
		(0..voter_pages).map(|i| {
			let page_field = page_field(i);

			let single = {
				let vote_filed = vote_filed(1);
				let push_code = from_impl_single_push_code();
				quote! {1 => #struct_name.#page_field.#vote_filed.#push_code,}
			};
			let double = {
				let vote_filed = vote_filed(2);
				let push_code = from_impl_double_push_code();
				quote! {2 => #struct_name.#page_field.#vote_filed.#push_code,}
			};
			let rest = {
				(3..=count)
					.map(|c| {
						let field = vote_filed(c);
						let push_code = from_impl_rest_push_code(c);
						quote!(#c => #struct_name.#page_field.#field.#push_code,)
					})
					.collect::<TokenStream2>()
			};

			quote!(
				#i => {
					match distribution.len() {
						0 => continue,
						#single
						#double
						#rest
						_ => {
							return Err(_npos::Error::SolutionTargetOverflow);
						}
					}
				},
			)
		})
	};

	let into_impl_per_page = {
		(0..voter_pages).map(|i| {
			let page_field = page_field(i);
			quote! {
				// overwrite the closure to mask the existence of pages.
				let voter_at = |voter_index: Self::Voter| voter_at_with_page(#i, voter_index);
				let this_page_assignment = self.#page_field.into_assignment(voter_at, &target_at)?;
				assignments.extend(this_page_assignment);
			}
		})
	};

	Ok(quote! {
		// NOTE: this will always simply derive Encode and Decode. The inner (per-page) type could
		// be `#[compact]` or not
		#[derive(Default, PartialEq, Eq, Clone, Debug, _npos::codec::Encode, _npos::codec::Decode)]
		#vis struct #ident {
			#paged_fields
		}

		impl _npos::MultiPageSolution for #ident {
			const PAGES: u8 = #voter_pages;

			/// Build self from a list of assignments.
			fn from_assignment<FV, FT, A>(
				assignments: &[_npos::Assignment<A, Self::Accuracy>],
				voter_page_and_index: FV,
				target_index: FT,
			) -> Result<Self, _npos::Error>
			where
				A: _npos::IdentifierT,
				for<'r> FV: Fn(&'r A) -> Option<(_npos::PageIndex, Self::Voter)>,
				for<'r> FT: Fn(&'r A) -> Option<Self::Target>,
				Self: Sized {
					let mut #struct_name: Self = Default::default();

					// populate `#struct_name`
					for _npos::Assignment { who, distribution } in assignments {
						let (page, voter_index_value) = voter_page_and_index(who).or_invalid_index()?;
						// convert `voter_index` into a closure that returns itself, this is a hack
						// to enable us to reuse code from single-page implementation. No need to
						// check the input, the code generated further down can ONLY use the `who`
						// variable, thus the correct index is `voter_index_value`.
						let voter_index = |_: &A| Some(voter_index_value);

						match page {
							#( #from_impl_per_page )*
							_ => return Err(_npos::Error::SolutionInvalidPageIndex)
						}
					}

					Ok(#struct_name)
				}

			/// Convert self into a `Vec<Assignment<A, Self::Accuracy>>`
			fn into_assignment<A: _npos::IdentifierT>(
				self,
				voter_at_with_page: impl Fn(_npos::PageIndex, Self::Voter) -> Option<A>,
				target_at: impl Fn(Self::Target) -> Option<A>,
			) -> Result<Vec<_npos::Assignment<A, Self::Accuracy>>, _npos::Error> {
				let mut assignments: _npos::sp_std::prelude::Vec<_npos::Assignment<A, #weight_type>> = Default::default();
				#( #into_impl_per_page )*
				Ok(assignments)
			}

			fn remove_voter(&mut self, remove_page: _npos::PageIndex, to_remove: Self::Voter) -> bool {
				match remove_page {
					#( #remove_voter_impl_per_page )*
					_ => false
				}
			}
		}

		impl _npos::SolutionBase for #ident {
			const LIMIT: usize = #count;
			type Voter = #voter_type;
			type Target = #target_type;
			type Accuracy = #weight_type;

			fn voter_count(&self) -> usize {
				#voter_count_impl
			}

			fn edge_count(&self) -> usize {
				#edge_count_impl
			}

			fn unique_targets(&self) -> _npos::sp_std::prelude::Vec<Self::Target> {
				#unique_targets_impl
			}
		}
	})
}
