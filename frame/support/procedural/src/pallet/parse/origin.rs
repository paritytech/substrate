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

use syn::spanned::Spanned;
use super::helper;

/// Definition of the pallet origin type.
///
/// Either:
/// * `type Origin`
/// * `struct Origin`
/// * `enum Origin`
pub struct OriginDef {
	/// The index of item in pallet module.
	pub index: usize,
	pub has_instance: bool,
	pub is_generic: bool,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
}

impl OriginDef {
	pub fn try_from(index: usize, item: &mut syn::Item) -> syn::Result<Self> {
		let item_span = item.span();
		let (vis, ident, generics) = match &item {
			syn::Item::Enum(item) => (&item.vis, &item.ident, &item.generics),
			syn::Item::Struct(item) => (&item.vis, &item.ident, &item.generics),
			syn::Item::Type(item) => (&item.vis, &item.ident, &item.generics),
			_ => {
				let msg = "Invalid pallet::origin, expected enum or struct or type";
				return Err(syn::Error::new(item.span(), msg));
			},
		};

		let has_instance = generics.params.len() == 2;
		let is_generic = generics.params.len() > 0;

		let mut instances = vec![];
		if let Some(u) = helper::check_type_def_optional_gen(&generics, item.span())? {
			instances.push(u);
		} else {
			// construct_runtime only allow generic event for instantiable pallet.
			instances.push(helper::InstanceUsage {
				has_instance: false,
				span: ident.span(),
			})
		}

		if !matches!(vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::origin, Origin must be public";
			return Err(syn::Error::new(item_span, msg));
		}

		if ident != "Origin" {
			let msg = "Invalid pallet::origin, ident must `Origin`";
			return Err(syn::Error::new(ident.span(), msg));
		}

		Ok(OriginDef {
			index,
			has_instance,
			is_generic,
			instances,
		})
	}
}
