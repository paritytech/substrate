// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse::Parse, ItemFn, LitInt, Result};

struct TransactionalLimit {
	limit: u8,
}

impl Default for TransactionalLimit {
	fn default() -> Self {
		Self { limit: 1 }
	}
}

impl Parse for TransactionalLimit {
	fn parse(input: syn::parse::ParseStream) -> Result<Self> {
		let limit: LitInt = input.parse()?;
		Ok(Self { limit: limit.base10_parse()? })
	}
}

pub fn transactional(attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let limit: TransactionalLimit = syn::parse(attr).unwrap_or_default();
	let limit = limit.limit;

	let ItemFn { attrs, vis, sig, block } = syn::parse(input)?;

	let crate_ = generate_crate_access_2018("frame-support")?;
	let output = quote! {
		#(#attrs)*
		#vis #sig {
			use #crate_::storage::with_storage_layer;
			// Otherwise, spawn a transaction layer.
			with_storage_layer(#limit, || {
				(|| { #block })()
			})
		}
	};

	Ok(output.into())
}

// Similar to `transactional` but only spawns at most 1 layer.
pub fn flat_transactional(attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let limit: TransactionalLimit = syn::parse(attr).unwrap_or_default();
	let limit = limit.limit;

	let ItemFn { attrs, vis, sig, block } = syn::parse(input)?;

	let crate_ = generate_crate_access_2018("frame-support")?;
	let output = quote! {
		#(#attrs)*
		#vis #sig {
			use #crate_::storage::{with_storage_layer, is_transactional};
			if is_transactional() {
				// We are already in a transaction layer, just execute the block.
				(|| { #block })()
			} else {
				// Otherwise, spawn a transaction layer.
				with_storage_layer(#limit, || {
					(|| { #block })()
				})
			}
		}
	};

	Ok(output.into())
}

pub fn require_transactional(_attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let ItemFn { attrs, vis, sig, block } = syn::parse(input)?;

	let crate_ = generate_crate_access_2018("frame-support")?;
	let output = quote! {
		#(#attrs)*
		#vis #sig {
			if !#crate_::storage::is_transactional(){
				return Err(DispatchError::TransactionLimitExceeded.into())
			}
			#block
		}
	};

	Ok(output.into())
}
