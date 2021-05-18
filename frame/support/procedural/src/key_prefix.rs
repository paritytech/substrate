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

use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use std::collections::BTreeSet;
use syn::{Ident, Result, Token, parse::Parser, punctuated::Punctuated};

pub fn impl_key_prefix_for(input: proc_macro::TokenStream) -> Result<TokenStream> {
	let args = Punctuated::<Ident, Token![,]>::parse_terminated.parse(input)?;
	let arity = args.len();
	if arity > 18 {
		let msg = "Only supports implementing for tuples up to 18 elements";
		return Err(syn::Error::new(args.last().unwrap().span(), msg));
	}

	let tuple_set = args
		.into_iter()
		.try_fold(BTreeSet::new(), |mut acc, ident| {
			let span = ident.span();
			if !acc.insert(ident) {
				return Err(syn::Error::new(span, "Duplicate identifier name"));
			}
			Ok(acc)
		})?;
	let mut prefix_set_iter = tuple_set.iter().rev().cloned().peekable();
	let mut suffix_set = Vec::new();

	let mut all_trait_impls = TokenStream::new();

	while let Some(next_ident) = prefix_set_iter.next() {
		if prefix_set_iter.peek().is_none() {
			break;
		}

		suffix_set.push(next_ident);
		let hashers = tuple_set.iter().map(|ident| format_ident!("Hasher{}", ident)).collect::<Vec<_>>();
		let kargs = prefix_set_iter.clone().map(|ident| format_ident!("KArg{}", ident)).collect::<Vec<_>>();
		let all_idents = &tuple_set;
		let prefixes = prefix_set_iter.clone().collect::<Vec<_>>();
		let partial_keygen = if suffix_set.len() == arity - 1 {
			let key = prefix_set_iter.peek().unwrap();
			let hasher = format_ident!("Hasher{}", key);

			quote!(Key<#hasher, #key>)
		} else {
			let keys = prefix_set_iter.clone();
			let hashers = keys.clone().map(|ident| format_ident!("Hasher{}", ident));

			quote!((#(Key<#hashers, #keys>),*))
		};
		let suffixes = if suffix_set.len() == 1 {
			suffix_set.iter().next().unwrap().to_token_stream()
		} else {
			let iter = suffix_set.iter();
			quote!((#(#iter),*))
		};
		let suffix_keygen = if suffix_set.len() == 1 {
			let key = suffix_set.iter().next().unwrap();
			let hasher = format_ident!("Hasher{}", key);

			quote!(Key<#hasher, #key>)
		} else {
			let keys = &suffix_set;
			let hashers = keys.iter().map(|ident| format_ident!("Hasher{}", ident));

			quote!((#(Key<#hashers, #keys>),*))
		};

		let trait_impls = quote!{
			impl<
				#(#all_idents: FullCodec,)*
				#(#hashers: StorageHasher,)*
				#(#kargs: EncodeLike<#prefixes>),*
			> HasKeyPrefix<(#(#kargs,)*)> for (#(Key<#hashers, #all_idents>,)*) {
				type Suffix = #suffixes;

				fn partial_key(prefix: (#(#kargs,)*)) -> Vec<u8> {
					<#partial_keygen>::final_key(prefix)
				}
			}

			impl<
				#(#all_idents: FullCodec,)*
				#(#hashers: ReversibleStorageHasher,)*
				#(#kargs: EncodeLike<#prefixes>),*
			> HasReversibleKeyPrefix<(#(#kargs,)*)> for (#(Key<#hashers, #all_idents>,)*) {
				fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
					<#suffix_keygen>::decode_final_key(key_material).map(|k| k.0)
				}
			}
		};

		all_trait_impls.extend(trait_impls);
	}

	Ok(all_trait_impls)
}
