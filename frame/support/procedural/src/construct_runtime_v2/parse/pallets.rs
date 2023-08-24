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
	construct_runtime::parse::Pallet, construct_runtime_v2::parse::pallet_decl::PalletDeclaration,
};
use std::collections::{HashMap, HashSet};
use syn::{spanned::Spanned, Ident};

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
	pub fn try_from(attr_span: proc_macro2::Span, item: &mut syn::Item) -> syn::Result<Self> {
		let item = if let syn::Item::Struct(item) = item {
			item
		} else {
			let msg = "Invalid frame::pallets, expected struct definition";
			return Err(syn::Error::new(item.span(), msg))
		};

		let name = item.ident.clone();

		let mut indices = HashMap::new();
		let mut names = HashMap::new();

		let mut last_index: Option<u8> = None;

		let mut pallet_decls = vec![];
		let mut pallets = vec![];

		for (index, item) in item.fields.iter_mut().enumerate() {
			match item.ty.clone() {
				syn::Type::Path(ref path) => {
					let pallet_decl = PalletDeclaration::try_from(attr_span, index, item, path)?;
					pallet_decls.push(pallet_decl);
				},
				syn::Type::TraitObject(syn::TypeTraitObject { bounds, .. }) => {
					let current_index = match last_index {
						Some(index) => index.checked_add(1).ok_or_else(|| {
							let msg = "Pallet index doesn't fit into u8, index is 256";
							syn::Error::new(name.span(), msg)
						}),
						None => Ok(0),
					}?;
					let pallet = Pallet::try_from(attr_span, current_index, item, &bounds)?;

					if let Some(used_pallet) = indices.insert(pallet.index, pallet.name.clone()) {
						let msg = format!(
							"Pallet indices are conflicting: Both pallets {} and {} are at index {}",
							used_pallet, pallet.name, pallet.index,
						);
						let mut err = syn::Error::new(used_pallet.span(), &msg);
						err.combine(syn::Error::new(pallet.name.span(), msg));
						return Err(err)
					}

					if let Some(used_pallet) = names.insert(pallet.name.clone(), pallet.name.span())
					{
						let msg = "Two pallets with the same name!";

						let mut err = syn::Error::new(used_pallet, &msg);
						err.combine(syn::Error::new(pallet.name.span(), &msg));
						return Err(err)
					}

					last_index = Some(pallet.index);
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
