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

use crate::{pallet::Def, COUNTER};
use syn::spanned::Spanned;

/// Generate the `construct_runtime_parts` macro.
pub fn expand_construct_runtime_parts(def: &mut Def) -> proc_macro2::TokenStream {
	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let construct_runtime_parts_unique_id =
		syn::Ident::new(&format!("__construct_runtime_parts_{}", count), def.item.span());

	let call_part = def.call.as_ref().map(|_| quote::quote!(Call,));

	let storage_part = (!def.storages.is_empty()).then(|| quote::quote!(Storage,));

	let event_part = def.event.as_ref().map(|event| {
		let gen = event.gen_kind.is_generic().then(|| quote::quote!( <T> ));
		quote::quote!( Event #gen , )
	});

	let origin_part = def.origin.as_ref().map(|origin| {
		let gen = origin.is_generic.then(|| quote::quote!( <T> ));
		quote::quote!( Origin #gen , )
	});

	let config_part = def.genesis_config.as_ref().map(|genesis_config| {
		let gen = genesis_config.gen_kind.is_generic().then(|| quote::quote!( <T> ));
		quote::quote!( Config #gen , )
	});

	let inherent_part = def.inherent.as_ref().map(|_| quote::quote!(Inherent,));

	let validate_unsigned_part =
		def.validate_unsigned.as_ref().map(|_| quote::quote!(ValidateUnsigned,));

	quote::quote!(
		// Export the construct runtime parts macro with a unique name to avoid conflict.
		//
		// macro args are:
		// ```
		// { $path_to_frame_support }
		// { $pattern_tokens }
		// $input
		// ```
		//
		// it will search in $input for the $pattern_tokens and then expand after it
		// `::{Part1, Part2, ..}`.
		#[macro_export]
		#[doc(hidden)]
		macro_rules! #construct_runtime_parts_unique_id {
			(
				{ $frame_support:tt }
				{ $( $pattern:tt )* }
				$( $t:tt )*
			) => {
				$frame_support::expand_after!(
					{ $( $pattern )* }
					{
						::{
							Pallet, #call_part #storage_part #event_part #origin_part #config_part
							#inherent_part #validate_unsigned_part
						}
					}
					$( $t )*
				);
			}
		}

		/// Macro to build the pallet parts inside `construct_runtime`.
		///
		/// This macro is expected to be called by `construct_runtime` when the pallet parts are
		/// not explicitly provided.
		pub use #construct_runtime_parts_unique_id as construct_runtime_parts;
	)
}
