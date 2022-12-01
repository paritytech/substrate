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

use crate::pallet::{Def, parse::helper::get_doc_literals};

/// * Add __Ignore variant on Event
/// * Impl various trait on Event including metadata
/// * if deposit_event is defined, implement deposit_event on module.
pub fn expand_event(def: &mut Def) -> proc_macro2::TokenStream {
	let event = if let Some(event) = &def.event {
		event
	} else {
		return Default::default()
	};

	let event_where_clause = &event.where_clause;

	// NOTE: actually event where clause must be a subset of config where clause because of
	// `type Event: From<Event<Self>>`. But we merge either way for potential better error message
	let completed_where_clause = super::merge_where_clauses(&[
		&event.where_clause,
		&def.config.where_clause,
	]);

	let event_ident = &event.event;
	let frame_system = &def.frame_system;
	let frame_support = &def.frame_support;
	let event_use_gen = &event.gen_kind.type_use_gen(event.attr_span);
	let event_impl_gen= &event.gen_kind.type_impl_gen(event.attr_span);
	let metadata = event.metadata.iter()
		.map(|(ident, args, docs)| {
			let name = format!("{}", ident);
			quote::quote_spanned!(event.attr_span =>
				#frame_support::event::EventMetadata {
					name: #frame_support::event::DecodeDifferent::Encode(#name),
					arguments: #frame_support::event::DecodeDifferent::Encode(&[
						#( #args, )*
					]),
					documentation: #frame_support::event::DecodeDifferent::Encode(&[
						#( #docs, )*
					]),
				},
			)
		});

	let event_item = {
		let item = &mut def.item.content.as_mut().expect("Checked by def parser").1[event.index];
		if let syn::Item::Enum(item) = item {
			item
		} else {
			unreachable!("Checked by event parser")
		}
	};

	// Phantom data is added for generic event.
	if event.gen_kind.is_generic() {
		let variant = syn::parse_quote!(
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				#frame_support::sp_std::marker::PhantomData<(#event_use_gen)>,
				#frame_support::Never,
			)
		);

		// Push ignore variant at the end.
		event_item.variants.push(variant);
	}

	if get_doc_literals(&event_item.attrs).is_empty() {
		event_item.attrs.push(syn::parse_quote!(
			#[doc = r"
			The [event](https://substrate.dev/docs/en/knowledgebase/runtime/events) emitted
			by this pallet.
			"]
		));
	}

	// derive some traits because system event require Clone, FullCodec, Eq, PartialEq and Debug
	event_item.attrs.push(syn::parse_quote!(
		#[derive(
			#frame_support::CloneNoBound,
			#frame_support::EqNoBound,
			#frame_support::PartialEqNoBound,
			#frame_support::RuntimeDebugNoBound,
			#frame_support::codec::Encode,
			#frame_support::codec::Decode,
		)]
	));

	let deposit_event = if let Some((fn_vis, fn_span)) = &event.deposit_event {
		let event_use_gen = &event.gen_kind.type_use_gen(event.attr_span);
		let trait_use_gen = &def.trait_use_generics(event.attr_span);
		let type_impl_gen = &def.type_impl_generics(event.attr_span);
		let type_use_gen = &def.type_use_generics(event.attr_span);

		quote::quote_spanned!(*fn_span =>
			impl<#type_impl_gen> Pallet<#type_use_gen> #completed_where_clause {
				#fn_vis fn deposit_event(event: Event<#event_use_gen>) {
					let event = <
						<T as Config#trait_use_gen>::Event as
						From<Event<#event_use_gen>>
					>::from(event);

					let event = <
						<T as Config#trait_use_gen>::Event as
						Into<<T as #frame_system::Config>::Event>
					>::into(event);

					<#frame_system::Pallet<T>>::deposit_event(event)
				}
			}
		)
	} else {
		Default::default()
	};

	quote::quote_spanned!(event.attr_span =>
		#deposit_event

		impl<#event_impl_gen> From<#event_ident<#event_use_gen>> for () #event_where_clause {
			fn from(_: #event_ident<#event_use_gen>) {}
		}

		impl<#event_impl_gen> #event_ident<#event_use_gen> #event_where_clause {
			#[allow(dead_code)]
			#[doc(hidden)]
			pub fn metadata() -> &'static [#frame_support::event::EventMetadata] {
				&[ #( #metadata )* ]
			}
		}
	)
}
