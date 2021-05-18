// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use std::collections::BTreeSet;
use syn::{Ident, Result};

const ALL_IDENTS: [&'static str; 18] =
	["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R"];

pub fn impl_key_prefix_for_tuples(input: proc_macro::TokenStream) -> Result<TokenStream> {
	if !input.is_empty() {
		return Err(syn::Error::new(Span::call_site(), "No arguments expected"));
	}

	let mut all_trait_impls = TokenStream::new();

	for i in 2..=18 {
		let current_tuple = ALL_IDENTS[0..i]
			.iter()
			.map(|s| Ident::new(s, Span::call_site()))
			.collect::<Vec<_>>();
		let mut prefix_iter = current_tuple.iter().rev().cloned().peekable();
		let mut suffix_set = BTreeSet::new();

		while let Some(next_ident) = prefix_iter.next() {
			if prefix_iter.peek().is_none() {
				break;
			}

			suffix_set.insert(next_ident);
			let hashers = current_tuple.iter().map(|ident| format_ident!("Hasher{}", ident)).collect::<Vec<_>>();
			let kargs = prefix_iter.clone().rev().map(|ident| format_ident!("KArg{}", ident)).collect::<Vec<_>>();
			let prefixes = prefix_iter.clone().rev().collect::<Vec<_>>();
			let partial_keygen = if suffix_set.len() == current_tuple.len() - 1 {
				let key = prefix_iter.peek().expect("Next element is guaranteed to not be empty; qed");
				let hasher = format_ident!("Hasher{}", key);

				quote!(Key<#hasher, #key>)
			} else {
				let keys = prefix_iter.clone().rev();
				let hashers = keys.clone().map(|ident| format_ident!("Hasher{}", ident));

				quote!((#(Key<#hashers, #keys>),*))
			};
			let suffixes = if suffix_set.len() == 1 {
				suffix_set.iter().next().expect("Next element is checked to not be empty; qed").to_token_stream()
			} else {
				quote!((#(#suffix_set),*))
			};
			let suffix_keygen = if suffix_set.len() == 1 {
				let key = suffix_set.iter().next().expect("Next element is checked to not be empty; qed");
				let hasher = format_ident!("Hasher{}", key);

				quote!(Key<#hasher, #key>)
			} else {
				let keys = &suffix_set;
				let hashers = keys.iter().map(|ident| format_ident!("Hasher{}", ident));

				quote!((#(Key<#hashers, #keys>),*))
			};

			let trait_impls = quote!{
				impl<
					#(#current_tuple: FullCodec,)*
					#(#hashers: StorageHasher,)*
					#(#kargs: EncodeLike<#prefixes>),*
				> HasKeyPrefix<(#(#kargs,)*)> for (#(Key<#hashers, #current_tuple>,)*) {
					type Suffix = #suffixes;

					fn partial_key(prefix: (#(#kargs,)*)) -> Vec<u8> {
						<#partial_keygen>::final_key(prefix)
					}
				}

				impl<
					#(#current_tuple: FullCodec,)*
					#(#hashers: ReversibleStorageHasher,)*
					#(#kargs: EncodeLike<#prefixes>),*
				> HasReversibleKeyPrefix<(#(#kargs,)*)> for (#(Key<#hashers, #current_tuple>,)*) {
					fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
						<#suffix_keygen>::decode_final_key(key_material).map(|k| k.0)
					}
				}
			};

			all_trait_impls.extend(trait_impls);
		}
	}

	Ok(all_trait_impls)
}
