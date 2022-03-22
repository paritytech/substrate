// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use syn::spanned::Spanned;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(DispatchResultWithPostInfo);
	syn::custom_keyword!(Call);
	syn::custom_keyword!(OriginFor);
	syn::custom_keyword!(weight);
	syn::custom_keyword!(compact);
	syn::custom_keyword!(T);
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(constant_name);
}

/// Definition of extra constants typically `impl<T: Config> Pallet<T> { ... }`
pub struct ExtraConstantsDef {
	/// The where_clause used.
	pub where_clause: Option<syn::WhereClause>,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The index of call item in pallet module.
	pub index: usize,
	/// The extra constant defined.
	pub extra_constants: Vec<ExtraConstantDef>,
}

/// Input definition for an constant in pallet.
pub struct ExtraConstantDef {
	/// Name of the function
	pub ident: syn::Ident,
	/// The type returned by the function
	pub type_: syn::Type,
	/// The doc associated
	pub doc: Vec<syn::Lit>,
	/// Optional MetaData Name
	pub metadata_name: Option<syn::Ident>,
}

/// Attributes for functions in extra_constants impl block.
/// Parse for `#[pallet::constant_name(ConstantName)]`
pub struct ExtraConstAttr {
	metadata_name: syn::Ident,
}

impl syn::parse::Parse for ExtraConstAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;
		content.parse::<keyword::constant_name>()?;

		let metadata_name;
		syn::parenthesized!(metadata_name in content);
		Ok(ExtraConstAttr { metadata_name: metadata_name.parse::<syn::Ident>()? })
	}
}

impl ExtraConstantsDef {
	pub fn try_from(index: usize, item: &mut syn::Item) -> syn::Result<Self> {
		let item = if let syn::Item::Impl(item) = item {
			item
		} else {
			return Err(syn::Error::new(
				item.span(),
				"Invalid pallet::extra_constants, expected item impl",
			))
		};

		let mut instances = vec![];
		instances.push(helper::check_impl_gen(&item.generics, item.impl_token.span())?);
		instances.push(helper::check_pallet_struct_usage(&item.self_ty)?);

		if let Some((_, _, for_)) = item.trait_ {
			let msg = "Invalid pallet::call, expected no trait ident as in \
				`impl<..> Pallet<..> { .. }`";
			return Err(syn::Error::new(for_.span(), msg))
		}

		let mut extra_constants = vec![];
		for impl_item in &mut item.items {
			let method = if let syn::ImplItem::Method(method) = impl_item {
				method
			} else {
				let msg = "Invalid pallet::call, only method accepted";
				return Err(syn::Error::new(impl_item.span(), msg))
			};

			if !method.sig.inputs.is_empty() {
				let msg = "Invalid pallet::extra_constants, method must have 0 args";
				return Err(syn::Error::new(method.sig.span(), msg))
			}

			if !method.sig.generics.params.is_empty() {
				let msg = "Invalid pallet::extra_constants, method must have 0 generics";
				return Err(syn::Error::new(method.sig.generics.params[0].span(), msg))
			}

			if method.sig.generics.where_clause.is_some() {
				let msg = "Invalid pallet::extra_constants, method must have no where clause";
				return Err(syn::Error::new(method.sig.generics.where_clause.span(), msg))
			}

			let type_ = match &method.sig.output {
				syn::ReturnType::Default => {
					let msg = "Invalid pallet::extra_constants, method must have a return type";
					return Err(syn::Error::new(method.span(), msg))
				},
				syn::ReturnType::Type(_, type_) => *type_.clone(),
			};

			// parse metadata_name
			let mut extra_constant_attrs: Vec<ExtraConstAttr> =
				helper::take_item_pallet_attrs(method)?;

			if extra_constant_attrs.len() > 1 {
				let msg =
					"Invalid attribute in pallet::constant_name, only one attribute is expected";
				return Err(syn::Error::new(extra_constant_attrs[1].metadata_name.span(), msg))
			}

			let metadata_name = extra_constant_attrs.pop().map(|attr| attr.metadata_name);

			extra_constants.push(ExtraConstantDef {
				ident: method.sig.ident.clone(),
				type_,
				doc: get_doc_literals(&method.attrs),
				metadata_name,
			});
		}

		Ok(Self {
			index,
			instances,
			where_clause: item.generics.where_clause.clone(),
			extra_constants,
		})
	}
}
