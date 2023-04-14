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
use syn::spanned::Spanned;

/// Definition of type value. Just a function which is expanded to a struct implementing `Get`.
pub struct TypeValueDef {
	/// The index of error item in pallet module.
	pub index: usize,
	/// Visibility of the struct to generate.
	pub vis: syn::Visibility,
	/// Ident of the struct to generate.
	pub ident: syn::Ident,
	/// The type return by Get.
	pub type_: Box<syn::Type>,
	/// The block returning the value to get
	pub block: Box<syn::Block>,
	/// If type value is generic over `T` (or `T` and `I` for instantiable pallet)
	pub is_generic: bool,
	/// A set of usage of instance, must be check for consistency with config.
	pub instances: Vec<helper::InstanceUsage>,
	/// The where clause of the function.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::type_value attribute.
	pub attr_span: proc_macro2::Span,
	/// Docs on the item.
	pub docs: Vec<syn::Expr>,
}

impl TypeValueDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Fn(item) = item {
			item
		} else {
			let msg = "Invalid pallet::type_value, expected item fn";
			return Err(syn::Error::new(item.span(), msg))
		};

		let mut docs = vec![];
		for attr in &item.attrs {
			if let syn::Meta::NameValue(meta) = &attr.meta {
				if meta.path.get_ident().map_or(false, |ident| ident == "doc") {
					docs.push(meta.value.clone());
					continue
				}
			}

			let msg = "Invalid pallet::type_value, unexpected attribute, only doc attribute are \
				allowed";
			return Err(syn::Error::new(attr.span(), msg))
		}

		if let Some(span) = item
			.sig
			.constness
			.as_ref()
			.map(|t| t.span())
			.or_else(|| item.sig.asyncness.as_ref().map(|t| t.span()))
			.or_else(|| item.sig.unsafety.as_ref().map(|t| t.span()))
			.or_else(|| item.sig.abi.as_ref().map(|t| t.span()))
			.or_else(|| item.sig.variadic.as_ref().map(|t| t.span()))
		{
			let msg = "Invalid pallet::type_value, unexpected token";
			return Err(syn::Error::new(span, msg))
		}

		if !item.sig.inputs.is_empty() {
			let msg = "Invalid pallet::type_value, unexpected argument";
			return Err(syn::Error::new(item.sig.inputs[0].span(), msg))
		}

		let vis = item.vis.clone();
		let ident = item.sig.ident.clone();
		let block = item.block.clone();
		let type_ = match item.sig.output.clone() {
			syn::ReturnType::Type(_, type_) => type_,
			syn::ReturnType::Default => {
				let msg = "Invalid pallet::type_value, expected return type";
				return Err(syn::Error::new(item.sig.span(), msg))
			},
		};

		let mut instances = vec![];
		if let Some(usage) = helper::check_type_value_gen(&item.sig.generics, item.sig.span())? {
			instances.push(usage);
		}

		let is_generic = item.sig.generics.type_params().count() > 0;
		let where_clause = item.sig.generics.where_clause.clone();

		Ok(TypeValueDef {
			attr_span,
			index,
			is_generic,
			vis,
			ident,
			block,
			type_,
			instances,
			where_clause,
			docs,
		})
	}
}
