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

mod call;
mod view;

use crate::interface::definition::parse::definition::{call::SingleCallDef, view::SingleViewDef};
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{AngleBracketedGenericArguments, GenericArgument, PathArguments};

pub struct InterfaceDef {
	index: usize,
	pub trait_name: syn::Ident,
	views: Option<view::ViewDef>,
	calls: Option<call::CallDef>,
	where_clause: Option<syn::WhereClause>,
	span: proc_macro2::Span,
}

impl InterfaceDef {
	pub fn calls(&self) -> (proc_macro2::Span, Option<syn::WhereClause>, Vec<SingleCallDef>) {
		if let Some(calls) = self.calls.as_ref() {
			(calls.interface_span, self.where_clause.clone(), calls.calls.clone())
		} else {
			(self.span.clone(), self.where_clause.clone(), Vec::new())
		}
	}

	pub fn views(&self) -> (proc_macro2::Span, Option<syn::WhereClause>, Vec<SingleViewDef>) {
		if let Some(views) = self.views.as_ref() {
			(views.interface_span, self.where_clause.clone(), views.views.clone())
		} else {
			(self.span.clone(), self.where_clause.clone(), Vec::new())
		}
	}

	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
		_frame_support: syn::Ident,
		frame_system: syn::Ident,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Trait(item) = item {
			item
		} else {
			return Err(syn::Error::new(
				attr_span,
				"Invalid #[interface::definition], expected item trait",
			));
		};

		let has_frame_suppert_core_supertrait = item.supertraits.iter().any(|s| {
			syn::parse2::<CoreBoundParse>(s.to_token_stream())
				.map_or(false, |b| b.0 == frame_system)
		});
		if !has_frame_suppert_core_supertrait {
			let found = if item.supertraits.is_empty() {
				"none".to_string()
			} else {
				let mut found = item
					.supertraits
					.iter()
					.fold(String::new(), |acc, s| format!("{}`{}`, ", acc, quote::quote!(#s)));
				found.pop();
				found.pop();
				found
			};

			let msg = format!(
				"Invalid interface::trait, expected explicit `{}::Config` as supertrait, \
				found {}. \
				(try `pub trait {}: frame_system::Config)",
				frame_system, found, item.ident
			);
			return Err(syn::Error::new(attr_span, msg));
		}

		// NOTE: Where clauses are allowed. We carry them to all impl blocks.
		//       But "extending" an interface gets harder, as carrying them over from
		//       extended traits is harder.

		// Ensure no generics on interface trait
		let item_span = item.span();
		if !item.generics.params.is_empty() {
			let msg = "Invalid Interface definition. Traits that define an interface \
                currently can not have generics.";
			return Err(syn::Error::new(item_span, msg));
		}
		let where_clause = item.generics.where_clause.clone();

		// Ensure not unsafe
		if item.unsafety.is_some() {
			let msg = "Invalid Interface definition. Traits that define an interface \
                can not be unsafe.";
			return Err(syn::Error::new(item_span, msg));
		}

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid Interface definition. Traits that define an interface \
                must be public.";
			return Err(syn::Error::new(item_span, msg));
		}

		let mut views = None;
		let mut calls = None;

		for (index, item) in item.items.iter_mut().enumerate() {
			let interface_attr: Option<InterfaceTraitAttr> =
				crate::interface::helper::take_first_item_interface_attr(item)?;

			match interface_attr {
				Some(InterfaceTraitAttr::Call(span)) => {
					calls = Some(call::CallDef::try_from(item_span, calls, span, index, item)?)
				},
				Some(InterfaceTraitAttr::View(span)) => {
					views = Some(view::ViewDef::try_from(item_span, views, span, index, item)?)
				},
				None => (),
			}
		}

		Ok(InterfaceDef {
			index,
			calls,
			views,
			where_clause,
			span: item.span(),
			trait_name: item.ident.clone(),
		})
	}
}

/// Parse for `$ident::interface::Core`
pub struct CoreBoundParse(syn::Ident);

impl syn::parse::Parse for CoreBoundParse {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let ident = input.parse::<syn::Ident>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::Config>()?;

		if input.peek(syn::token::Lt) {
			input.parse::<syn::AngleBracketedGenericArguments>()?;
		}

		Ok(Self(ident))
	}
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(Config);
	syn::custom_keyword!(call);
	syn::custom_keyword!(view);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::call]`)
enum InterfaceTraitAttr {
	Call(proc_macro2::Span),
	View(proc_macro2::Span),
}

impl syn::parse::Parse for InterfaceTraitAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::call) {
			Ok(InterfaceTraitAttr::Call(content.parse::<keyword::call>()?.span()))
		} else if lookahead.peek(keyword::view) {
			Ok(InterfaceTraitAttr::View(content.parse::<keyword::view>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}

fn adapt_type_to_generic_if_self(ty: Box<syn::Type>) -> Box<syn::Type> {
	let mut type_path = if let syn::Type::Path(path) = *ty { path } else { return ty };

	// Replace the `Self` in qualified path if existing
	if let Some(q_self) = &type_path.qself {
		let ty = adapt_type_to_generic_if_self(q_self.ty.clone());

		type_path.qself = Some(syn::QSelf {
			lt_token: q_self.lt_token,
			ty,
			position: q_self.position,
			as_token: q_self.as_token,
			gt_token: q_self.gt_token,
		});
	}

	for segment in type_path.path.segments.iter_mut() {
		if segment.ident == "Self" {
			let rt_ident = syn::Ident::new("Runtime", proc_macro2::Span::call_site());
			segment.ident = rt_ident;
		}

		if let PathArguments::AngleBracketed(generic) = &mut segment.arguments {
			for argument in &mut generic.args {
				if let GenericArgument::Type(ty) = argument {
					*ty = *adapt_type_to_generic_if_self(Box::new(ty.clone()));
				}
			}
		}
	}

	Box::new(syn::Type::Path(type_path))
}
