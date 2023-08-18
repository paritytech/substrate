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

use crate::construct_runtime::parse::{Pallet, PalletPart, PalletPath};
use quote::ToTokens;
use syn::{punctuated::Punctuated, spanned::Spanned, token, Error};

impl Pallet {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &syn::Field,
		bounds: &Punctuated<syn::TypeParamBound, token::Plus>,
	) -> syn::Result<Self> {
		let name = item
			.ident
			.clone()
			.ok_or(Error::new(attr_span, "Invalid pallet declaration, expected a named field"))?;

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

		let cfg_pattern = vec![];

		Ok(Pallet {
			is_expanded: true,
			name,
			index: index as u8,
			path,
			instance,
			cfg_pattern,
			pallet_parts,
		})
	}
}
