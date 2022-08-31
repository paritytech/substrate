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

/// Definition for pallet genesis build implementation.
pub struct GenesisBuildDef {
	/// The index of item in pallet module.
	pub index: usize,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The where_clause used.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::genesis_build attribute.
	pub attr_span: proc_macro2::Span,
}

impl GenesisBuildDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Impl(item) = item {
			item
		} else {
			let msg = "Invalid pallet::genesis_build, expected item impl";
			return Err(syn::Error::new(item.span(), msg));
		};

		let item_trait = &item.trait_.as_ref()
			.ok_or_else(|| {
				let msg = "Invalid pallet::genesis_build, expected impl<..> GenesisBuild<..> \
					for GenesisConfig<..>";
				syn::Error::new(item.span(), msg)
			})?.1;

		let mut instances = vec![];
		instances.push(helper::check_genesis_builder_usage(&item_trait)?);

		Ok(Self {
			attr_span,
			index,
			instances,
			where_clause: item.generics.where_clause.clone(),
		})
	}
}
