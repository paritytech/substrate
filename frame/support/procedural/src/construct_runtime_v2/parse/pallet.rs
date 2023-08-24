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

use crate::construct_runtime::parse::{Pallet, PalletPart, PalletPartKeyword, PalletPath};
use quote::ToTokens;
use syn::{punctuated::Punctuated, spanned::Spanned, token, Error};

mod keyword {
	syn::custom_keyword!(frame);
	syn::custom_keyword!(pallet_index);
	syn::custom_keyword!(disable_call);
}

enum PalletAttr {
	PalletIndex(proc_macro2::Span, u8),
	DisableCall(proc_macro2::Span),
}

impl PalletAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::PalletIndex(span, _) => *span,
			Self::DisableCall(span) => *span,
		}
	}
}

impl syn::parse::Parse for PalletAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::frame>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::pallet_index) {
			let _ = content.parse::<keyword::pallet_index>();
			let pallet_index_content;
			syn::parenthesized!(pallet_index_content in content);
			let pallet_index = pallet_index_content.parse::<syn::LitInt>()?;
			if !pallet_index.suffix().is_empty() {
				let msg = "Number literal must not have a suffix";
				return Err(syn::Error::new(pallet_index.span(), msg))
			}
			Ok(PalletAttr::PalletIndex(pallet_index.span(), pallet_index.base10_parse()?))
		} else if lookahead.peek(keyword::disable_call) {
			Ok(PalletAttr::DisableCall(content.parse::<keyword::disable_call>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}

fn take_first_item_pallet_attr<Attr>(item: &mut syn::Field) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = &mut item.attrs;

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path().segments.first().map_or(false, |segment| segment.ident == "frame")
	}) {
		let runtime_attr = attrs.remove(index);
		Ok(Some(syn::parse2(runtime_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

impl Pallet {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: u8,
		item: &mut syn::Field,
		bounds: &Punctuated<syn::TypeParamBound, token::Plus>,
	) -> syn::Result<Self> {
		let name = item
			.ident
			.clone()
			.ok_or(Error::new(attr_span, "Invalid pallet declaration, expected a named field"))?;

		let mut pallet_index = index;
		let mut disable_call = false;

		while let Some(pallet_attr) = take_first_item_pallet_attr::<PalletAttr>(item)? {
			match pallet_attr {
				PalletAttr::PalletIndex(_, index) => pallet_index = index,
				PalletAttr::DisableCall(_) => disable_call = true,
			}
		}

		let mut pallet_path = None;
		let mut pallet_parts = vec![];

		for (index, bound) in bounds.into_iter().enumerate() {
			if let syn::TypeParamBound::Trait(syn::TraitBound { path, .. }) = bound {
				if index == 0 {
					pallet_path = Some(PalletPath { inner: path.clone() });
				} else {
					let pallet_part = syn::parse2::<PalletPart>(bound.into_token_stream())?;
					pallet_parts.push(pallet_part);
				}
			} else {
				return Err(Error::new(
					attr_span,
					"Invalid pallet declaration, expected a path or a trait object",
				))
			};
		}

		let mut path = pallet_path.ok_or(Error::new(
			attr_span,
			"Invalid pallet declaration, expected a path or a trait object",
		))?;

		let mut instance = None;
		// Todo: revisit this
		if let Some(segment) = path.inner.segments.iter_mut().find(|seg| !seg.arguments.is_empty())
		{
			if let syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
				args,
				..
			}) = segment.arguments.clone()
			{
				if let Some(syn::GenericArgument::Type(syn::Type::Path(arg_path))) = args.first() {
					instance = Some(syn::Ident::new(
						&arg_path.to_token_stream().to_string(),
						arg_path.span(),
					));
					segment.arguments = syn::PathArguments::None;
				}
			}
		}

		if disable_call {
			pallet_parts =
				pallet_parts
					.into_iter()
					.filter(|part| {
						if let PalletPartKeyword::Call(_) = part.keyword {
							false
						} else {
							true
						}
					})
					.collect();
		}

		let cfg_pattern = vec![];

		Ok(Pallet {
			is_expanded: true,
			name,
			index: pallet_index,
			path,
			instance,
			cfg_pattern,
			pallet_parts,
		})
	}
}
