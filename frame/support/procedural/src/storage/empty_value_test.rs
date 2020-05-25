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

//! Implementation of some test. Test assert default value (for storage with default value) doesn't
//! encode to an empty slice.

use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use super::DeclStorageDefExt;

pub fn impl_empty_value_test(scrate: &TokenStream, def: &DeclStorageDefExt) -> TokenStream {
	// If there is `Option<()>` or `()` return compile error
	let unit_type = syn::Type::Tuple(syn::TypeTuple {
		paren_token: Default::default(),
		elems: syn::punctuated::Punctuated::new(),
	});
	for line in &def.storage_lines {
		if line.value_type == unit_type {
			return syn::Error::new(
				line.value_type.span(),
				"`()` is not supported, because storage doesn't support inserting empty values."
			).to_compile_error();
		}
	}

	// Otherwise implement some runtime tests
	let mut tests = TokenStream::new();

	for line in def.storage_lines.iter().filter(|l| !l.is_option && !l.is_generic) {
		let test_name = syn::Ident::new(
			&format!("test_default_value_for_{}_is_not_empty", line.name.to_string()),
			line.name.span(),
		);
		let value_type = &line.value_type;
		let default_value = line.default_value.as_ref().map(|d| quote!( #d ))
			.unwrap_or_else(|| quote!( Default::default() ));
		tests.extend(quote!{
			#[test]
			fn #test_name() {
				use #scrate::codec::Encode;
				let value: #value_type = #default_value;
				assert!(!value.encode().is_empty());
			}
		});
	}

	quote!(
		#[cfg(test)]
		#[allow(non_snake_case)]
		mod _decl_storage_assert_non_empty_value_tests {
			use super::*;

			#tests
		}
	)
}
