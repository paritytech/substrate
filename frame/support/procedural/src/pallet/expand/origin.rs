// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::{pallet::Def, COUNTER};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{spanned::Spanned, Ident};

pub fn expand_origins(def: &mut Def) -> TokenStream {
	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let macro_ident = Ident::new(&format!("__is_origin_part_defined_{}", count), def.item.span());

	let maybe_compile_error = if def.origin.is_none() {
		quote! {
			compile_error!(concat!(
				"`",
				stringify!($pallet_name),
				"` does not have #[pallet::origin] defined, perhaps you should \
				remove `Origin` from construct_runtime?",
			));
		}
	} else {
		TokenStream::new()
	};

	quote! {
		#[doc(hidden)]
		pub mod __substrate_origin_check {
			#[macro_export]
			#[doc(hidden)]
			macro_rules! #macro_ident {
				($pallet_name:ident) => {
					#maybe_compile_error
				}
			}

			#[doc(hidden)]
			pub use #macro_ident as is_origin_part_defined;
		}
	}
}
