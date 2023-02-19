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

use super::helper;
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use syn::{spanned::Spanned, Fields};

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(Error);
}

/// Records information about the error enum variants.
pub struct VariantField {
	/// Whether or not the field is named, i.e. whether it is a tuple variant or struct variant.
	pub is_named: bool,
}

/// This checks error declaration as a enum declaration with only variants without fields nor
/// discriminant.
pub struct ErrorDef {
	/// The index of error item in pallet module.
	pub index: usize,
	/// Variants ident, optional field and doc literals (ordered as declaration order)
	pub variants: Vec<(syn::Ident, Option<VariantField>, Vec<syn::Lit>)>,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The keyword error used (contains span).
	pub error: keyword::Error,
	/// The span of the pallet::error attribute.
	pub attr_span: proc_macro2::Span,
}

impl ErrorDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Enum(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::error, expected item enum"))
		};
		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::error, `Error` must be public";
			return Err(syn::Error::new(item.span(), msg))
		}

		let instances =
			vec![helper::check_type_def_gen_no_bounds(&item.generics, item.ident.span())?];

		if item.generics.where_clause.is_some() {
			let msg = "Invalid pallet::error, where clause is not allowed on pallet error item";
			return Err(syn::Error::new(item.generics.where_clause.as_ref().unwrap().span(), msg))
		}

		let error = syn::parse2::<keyword::Error>(item.ident.to_token_stream())?;

		let variants = item
			.variants
			.iter()
			.map(|variant| {
				let field_ty = match &variant.fields {
					Fields::Unit => None,
					Fields::Named(_) => Some(VariantField { is_named: true }),
					Fields::Unnamed(_) => Some(VariantField { is_named: false }),
				};
				if variant.discriminant.is_some() {
					let msg = "Invalid pallet::error, unexpected discriminant, discriminants \
						are not supported";
					let span = variant.discriminant.as_ref().unwrap().0.span();
					return Err(syn::Error::new(span, msg))
				}

				Ok((variant.ident.clone(), field_ty, get_doc_literals(&variant.attrs)))
			})
			.collect::<Result<_, _>>()?;

		Ok(ErrorDef { attr_span, index, variants, instances, error })
	}
}
