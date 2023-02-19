// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Helpers to generate the push code for `from_assignment` implementations. This can be shared
//! between both single_page and double_page, thus extracted here.
//!
//! All of the code in this helper module assumes some variable names, namely `who` and
//! `distribution`.

use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

pub(crate) fn from_impl_single_push_code() -> TokenStream2 {
	quote!(push((
		voter_index(&who).or_invalid_index()?,
		target_index(&distribution[0].0).or_invalid_index()?,
	)))
}

pub(crate) fn from_impl_rest_push_code(count: usize) -> TokenStream2 {
	let inner = (0..count - 1).map(|i| {
		quote!(
			(
				target_index(&distribution[#i].0).or_invalid_index()?,
				distribution[#i].1
			)
		)
	});

	let last_index = count - 1;
	let last = quote!(target_index(&distribution[#last_index].0).or_invalid_index()?);

	quote!(
		push(
			(
				voter_index(&who).or_invalid_index()?,
				[ #( #inner ),* ],
				#last,
			)
		)
	)
}
