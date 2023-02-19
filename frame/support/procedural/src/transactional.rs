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

use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro::TokenStream;
use quote::quote;
use syn::{ItemFn, Result};

pub fn transactional(_attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let ItemFn { attrs, vis, sig, block } = syn::parse(input)?;

	let crate_ = generate_crate_access_2018("frame-support")?;
	let output = quote! {
		#(#attrs)*
		#vis #sig {
			use #crate_::storage::{with_transaction, TransactionOutcome};
			with_transaction(|| {
				let r = (|| { #block })();
				if r.is_ok() {
					TransactionOutcome::Commit(r)
				} else {
					TransactionOutcome::Rollback(r)
				}
			})
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
			if !#crate_::storage::transactional::is_transactional() {
				return Err(#crate_::sp_runtime::TransactionalError::NoLayer.into());
			}
			#block
		}
	};

	Ok(output.into())
}
