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
// limitations under the License

use crate::construct_runtime::{Pallet, SYSTEM_PALLET_NAME};
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

pub fn expand_outer_event(
	runtime: &Ident,
	pallet_decls: &[Pallet],
	scrate: &TokenStream,
) -> syn::Result<TokenStream> {
	let mut event_variants = TokenStream::new();
	let mut event_conversions = TokenStream::new();
	let mut query_event_part_macros = Vec::new();

	for pallet_decl in pallet_decls {
		if pallet_decl.exists_part("Event") {
			let path = &pallet_decl.path;
			let pallet_name = &pallet_decl.name;
			let index = pallet_decl.index;

			let pallet_event = if pallet_decl.name == SYSTEM_PALLET_NAME {
				// Note: for some reason, the compiler recognizes
				// `<frame_system::Pallet<Runtime> as frame_system::SubstratePalletEvent>::Event` as essentially
				// the same as the outer/runtime Event type, which then causes an error about conflicting
				// implementations of the From<Event> trait for the Event type, and thereby necessitating a special
				// case for the system pallet.
				quote!(#path::Event<#runtime>)
			} else {
				let instance = pallet_decl.instance.as_ref().into_iter();
				quote!(<#path::Pallet<#runtime #(, #path::#instance)*> as #path::SubstratePalletEvent>::Event)
			};

			event_variants.extend(quote!(#[codec(index = #index)] #pallet_name(#pallet_event),));
			event_conversions.extend(expand_event_conversion(scrate, pallet_decl, &pallet_event));
			query_event_part_macros.push(quote! {
				#path::__substrate_event_check::is_event_part_defined!(#pallet_name);
			});
		}
	}

	Ok(quote! {
		#( #query_event_part_macros )*

		#[derive(
			Clone, PartialEq, Eq,
			#scrate::codec::Encode,
			#scrate::codec::Decode,
			#scrate::RuntimeDebug,
		)]
		#[allow(non_camel_case_types)]
		pub enum Event {
			#event_variants
		}

		#event_conversions
	})
}

fn expand_event_conversion(
	scrate: &TokenStream,
	pallet: &Pallet,
	pallet_event: &TokenStream,
) -> TokenStream {
	let variant_name = &pallet.name;

	quote! {
		impl From<#pallet_event> for Event {
			fn from(x: #pallet_event) -> Self {
				Event::#variant_name(x)
			}
		}
		impl #scrate::sp_std::convert::TryInto<#pallet_event> for Event {
			type Error = ();

			fn try_into(self) -> #scrate::sp_std::result::Result<#pallet_event, Self::Error> {
				match self {
					Self::#variant_name(evt) => Ok(evt),
					_ => Err(()),
				}
			}
		}
	}
}
