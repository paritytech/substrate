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
use std::collections::{HashMap, HashSet};
use syn::{
	punctuated::Punctuated, spanned::Spanned, token, Attribute, Error, GenericArgument, Ident,
};

#[derive(Debug, Clone)]
pub enum AllPalletsDeclaration {
	Implicit(ImplicitAllPalletsDeclaration),
	Explicit(ExplicitAllPalletsDeclaration),
}

/// Declaration of a runtime with some pallet with implicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ImplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallet_decls: Vec<PalletDeclaration>,
	pub pallet_count: usize,
}

/// Declaration of a runtime with all pallet having explicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ExplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallets: Vec<Pallet>,
}

impl AllPalletsDeclaration {
	// Todo: Check for indices and name conflicts.
	pub fn try_from(attr_span: proc_macro2::Span, item: &mut syn::Item) -> syn::Result<Self> {
		let item = if let syn::Item::Struct(item) = item {
			item
		} else {
			let msg = "Invalid frame::pallets, expected struct definition";
			return Err(syn::Error::new(item.span(), msg))
		};

		let name = item.ident.clone();
		let mut pallet_decls = vec![];
		let mut pallets = vec![];

		for (index, item) in item.fields.iter().enumerate() {
			match item.ty.clone() {
				syn::Type::Path(ref path) => {
					let pallet_decl = PalletDeclaration::try_from(attr_span, index, item, path)?;
					pallet_decls.push(pallet_decl);
				},
				syn::Type::TraitObject(syn::TypeTraitObject { bounds, .. }) => {
					let pallet = Pallet::try_from(attr_span, index, item, &bounds)?;
					pallets.push(pallet);
				},
				_ => continue,
			}
		}

		let decl_count = pallet_decls.len();
		if decl_count > 0 {
			Ok(AllPalletsDeclaration::Implicit(ImplicitAllPalletsDeclaration {
				name,
				pallet_decls,
				pallet_count: decl_count.saturating_add(pallets.len()),
			}))
		} else {
			Ok(AllPalletsDeclaration::Explicit(ExplicitAllPalletsDeclaration { name, pallets }))
		}
	}
}

/// The declaration of a pallet.
#[derive(Debug, Clone)]
pub struct PalletDeclaration {
	/// The name of the pallet, e.g.`System` in `System: frame_system`.
	pub name: Ident,
	/// Optional attributes tagged right above a pallet declaration.
	pub attrs: Vec<Attribute>,
	/// Optional fixed index, e.g. `MyPallet ...  = 3,`.
	pub index: Option<u8>,
	/// The path of the pallet, e.g. `frame_system` in `System: frame_system`.
	pub path: syn::Path,
	/// The instance of the pallet, e.g. `Instance1` in `Council: pallet_collective::<Instance1>`.
	pub instance: Option<Ident>,
}

impl PalletDeclaration {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &syn::Field,
		path: &syn::TypePath,
	) -> syn::Result<Self> {
		let name = item
			.ident
			.clone()
			.ok_or(Error::new(attr_span, "Invalid pallet declaration, expected a named field"))?;

		let mut path = path.path.clone();

		let mut instance = None;
		// Todo: revisit this
		if let Some(segment) = path.segments.iter_mut().find(|seg| !seg.arguments.is_empty()) {
			if let syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
				args,
				..
			}) = segment.arguments.clone()
			{
				if let Some(GenericArgument::Type(syn::Type::Path(arg_path))) = args.first() {
					instance = Some(syn::Ident::new(
						&arg_path.to_token_stream().to_string(),
						arg_path.span(),
					));
					segment.arguments = syn::PathArguments::None;
				}
			}
		}

		let index = Some(index as u8);

		Ok(Self { name, path, instance, index, attrs: item.attrs.clone() })
	}
}

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
				if let Some(GenericArgument::Type(syn::Type::Path(arg_path))) = args.first() {
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
