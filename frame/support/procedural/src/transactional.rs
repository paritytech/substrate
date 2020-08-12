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

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

pub fn transactional(_attr: TokenStream, input: TokenStream) -> TokenStream {
	let ItemFn { attrs, vis, sig, block } = parse_macro_input!(input as ItemFn);

	let output = quote! {
		#(#attrs)*
        #vis #sig {
			use frame_support::storage::{with_transaction, TransactionOutcome};
			with_transaction(|| {
				let r = #block;
				if r.is_ok() {
					TransactionOutcome::Commit(r)
				} else {
					TransactionOutcome::Rollback(r)
				}
			})
        }
    };
    output.into()
}
