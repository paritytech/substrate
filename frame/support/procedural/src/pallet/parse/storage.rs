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

use super::helper;
use syn::spanned::Spanned;
use quote::ToTokens;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(Error);
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(getter);
	syn::custom_keyword!(OptionQuery);
	syn::custom_keyword!(ValueQuery);
}

/// Parse for `#[pallet::getter(fn dummy)]`
pub struct PalletStorageAttr {
	getter: syn::Ident,
}

impl syn::parse::Parse for PalletStorageAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;
		content.parse::<keyword::getter>()?;

		let generate_content;
		syn::parenthesized!(generate_content in content);
		generate_content.parse::<syn::Token![fn]>()?;
		Ok(Self { getter: generate_content.parse::<syn::Ident>()? })
	}
}

/// The value and key types used by storages. Needed to expand metadata.
pub enum Metadata{
	Value { value: syn::GenericArgument },
	Map { value: syn::GenericArgument, key: syn::GenericArgument },
	DoubleMap {
		value: syn::GenericArgument,
		key1: syn::GenericArgument,
		key2: syn::GenericArgument
	},
}

pub enum QueryKind {
	OptionQuery,
	ValueQuery,
}

/// Definition of a storage, storage is a storage type like
/// `type MyStorage = StorageValue<MyStorageP, u32>`
/// The keys and values types are parsed in order to get metadata
pub struct StorageDef {
	/// The index of error item in pallet module.
	pub index: usize,
	/// Visibility of the storage type.
	pub vis: syn::Visibility,
	/// The type ident, to generate the StoragePrefix for.
	pub ident: syn::Ident,
	/// The keys and value metadata of the storage.
	pub metadata: Metadata,
	/// The doc associated to the storage.
	pub docs: Vec<syn::Lit>,
	/// A set of usage of instance, must be check for consistency with config.
	pub instances: Vec<helper::InstanceUsage>,
	/// Optional getter to generate. If some then query_kind is ensured to be some as well.
	pub getter: Option<syn::Ident>,
	/// Whereas the querytype of the storage is OptionQuery or ValueQuery.
	/// Note that this is best effort as it can't be determined when QueryKind is generic, and
	/// result can be false if user do some unexpected type alias.
	pub query_kind: Option<QueryKind>,
	/// Where clause of type definition.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::storage attribute.
	pub attr_span: proc_macro2::Span,
}

/// In `Foo<A, B, C>` retrieve the argument at given position, i.e. A is argument at position 0.
fn retrieve_arg(
	segment: &syn::PathSegment,
	arg_pos: usize,
) -> syn::Result<syn::GenericArgument> {
	if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
		if arg_pos < args.args.len() {
			Ok(args.args[arg_pos].clone())
		} else {
			let msg = format!("pallet::storage unexpected number of generic argument, expected at \
				least {} args, found {}", arg_pos + 1, args.args.len());
			Err(syn::Error::new(args.span(), msg))
		}
	} else {
		let msg = format!("pallet::storage unexpected number of generic argument, expected at \
			least {} args, found none", arg_pos + 1);
		Err(syn::Error::new(segment.span(), msg))
	}
}

impl StorageDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Type(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::storage, expected item type"));
		};

		let mut attrs: Vec<PalletStorageAttr> = helper::take_item_attrs(&mut item.attrs)?;
		if attrs.len() > 1 {
			let msg = "Invalid pallet::storage, multiple argument pallet::getter found";
			return Err(syn::Error::new(attrs[1].getter.span(), msg));
		}
		let getter = attrs.pop().map(|attr| attr.getter);

		let mut instances = vec![];
		instances.push(helper::check_type_def_gen(&item.generics, item.ident.span())?);

		let where_clause = item.generics.where_clause.clone();
		let docs = helper::get_doc_literals(&item.attrs);

		let typ = if let syn::Type::Path(typ) = &*item.ty {
			typ
		} else {
			let msg = "Invalid pallet::storage, expected type path";
			return Err(syn::Error::new(item.ty.span(), msg));
		};

		if typ.path.segments.len() != 1 {
			let msg = "Invalid pallet::storage, expected type path with one segment";
			return Err(syn::Error::new(item.ty.span(), msg));
		}

		let query_kind;
		let metadata = match &*typ.path.segments[0].ident.to_string() {
			"StorageValue" => {
				query_kind = retrieve_arg(&typ.path.segments[0], 2);
				Metadata::Value {
					value: retrieve_arg(&typ.path.segments[0], 1)?,
				}
			}
			"StorageMap" => {
				query_kind = retrieve_arg(&typ.path.segments[0], 4);
				Metadata::Map {
					key: retrieve_arg(&typ.path.segments[0], 2)?,
					value: retrieve_arg(&typ.path.segments[0], 3)?,
				}
			}
			"StorageDoubleMap" => {
				query_kind = retrieve_arg(&typ.path.segments[0], 6);
				Metadata::DoubleMap {
					key1: retrieve_arg(&typ.path.segments[0], 2)?,
					key2: retrieve_arg(&typ.path.segments[0], 4)?,
					value: retrieve_arg(&typ.path.segments[0], 5)?,
				}
			}
			found => {
				let msg = format!(
					"Invalid pallet::storage, expected ident: `StorageValue` or \
					`StorageMap` or `StorageDoubleMap` in order to expand metadata, found \
					`{}`",
					found,
				);
				return Err(syn::Error::new(item.ty.span(), msg));
			}
		};
		let query_kind = query_kind
			.map(|query_kind| match query_kind {
				syn::GenericArgument::Type(syn::Type::Path(path))
					if path.path.segments.last().map_or(false, |s| s.ident == "OptionQuery")
				=> Some(QueryKind::OptionQuery),
				syn::GenericArgument::Type(syn::Type::Path(path))
					if path.path.segments.last().map_or(false, |s| s.ident == "ValueQuery")
				=> Some(QueryKind::ValueQuery),
				_ => None,
			})
			.unwrap_or(Some(QueryKind::OptionQuery)); // This value must match the default generic.

		if query_kind.is_none() && getter.is_some() {
			let msg = "Invalid pallet::storage, cannot generate getter because QueryKind is not \
				identifiable. QueryKind must be `OptionQuery`, `ValueQuery`, or default one to be \
				identifiable.";
			return Err(syn::Error::new(getter.unwrap().span(), msg));
		}

		let prefix_arg = retrieve_arg(&typ.path.segments[0], 0)?;
		syn::parse2::<syn::Token![_]>(prefix_arg.to_token_stream())
			.map_err(|e| {
				let msg = "Invalid use of `#[pallet::storage]`, the type first generic argument \
					must be `_`, the final argument is automatically set by macro.";
				let mut err = syn::Error::new(prefix_arg.span(), msg);
				err.combine(e);
				err
			})?;

		Ok(StorageDef {
			attr_span,
			index,
			vis: item.vis.clone(),
			ident: item.ident.clone(),
			instances,
			metadata,
			docs,
			getter,
			query_kind,
			where_clause,
		})
	}
}
