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

use crate::{
	pallet::{CompositeKeyword, Def},
	COUNTER,
};
use syn::spanned::Spanned;

/// Generate the `tt_default_parts` macro.
pub fn expand_tt_default_parts(def: &mut Def) -> proc_macro2::TokenStream {
	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let default_parts_unique_id =
		syn::Ident::new(&format!("__tt_default_parts_{}", count), def.item.span());

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

	let freeze_reason_part = def
		.composites
		.iter()
		.any(|c| matches!(c.composite_keyword, CompositeKeyword::FreezeReason(_)))
		.then_some(quote::quote!(FreezeReason,));

	let hold_reason_part = def
		.composites
		.iter()
		.any(|c| matches!(c.composite_keyword, CompositeKeyword::HoldReason(_)))
		.then_some(quote::quote!(HoldReason,));

	let lock_id_part = def
		.composites
		.iter()
		.any(|c| matches!(c.composite_keyword, CompositeKeyword::LockId(_)))
		.then_some(quote::quote!(LockId,));

	let slash_reason_part = def
		.composites
		.iter()
		.any(|c| matches!(c.composite_keyword, CompositeKeyword::SlashReason(_)))
		.then_some(quote::quote!(SlashReason,));

	quote::quote!(
		// This macro follows the conventions as laid out by the `tt-call` crate. It does not
		// accept any arguments and simply returns the pallet parts, separated by commas, then
		// wrapped inside of braces and finally prepended with double colons, to the caller inside
		// of a key named `tokens`.
		//
		// We need to accept a frame_support argument here, because this macro gets expanded on the
		// crate that called the `construct_runtime!` macro, and said crate may have renamed
		// frame-support, and so we need to pass in the frame-support path that said crate
		// recognizes.
		#[macro_export]
		#[doc(hidden)]
		macro_rules! #default_parts_unique_id {
			{
				$caller:tt
				frame_support = [{ $($frame_support:ident)::* }]
			} => {
				$($frame_support)*::tt_return! {
					$caller
					tokens = [{
						::{
							Pallet, #call_part #storage_part #event_part #origin_part #config_part
							#inherent_part #validate_unsigned_part #freeze_reason_part
							#hold_reason_part #lock_id_part #slash_reason_part
						}
					}]
				}
			};
		}

		pub use #default_parts_unique_id as tt_default_parts;
	)
}
