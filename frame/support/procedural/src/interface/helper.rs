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

use quote::ToTokens;

/// Trait implemented for syn items to get mutable references on their attributes.
///
/// NOTE: verbatim variants are not supported.
pub trait MutItemAttrs {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>>;
}

/// Take the first interface attribute (e.g. attribute like `#[interface..]`) and decode it to
/// `Attr`
pub fn take_first_item_interface_attr<Attr>(
	item: &mut impl MutItemAttrs,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = item.mut_item_attrs() { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path.segments.first().map_or(false, |segment| segment.ident == "interface")
	}) {
		let interface_attr = attrs.remove(index);
		Ok(Some(syn::parse2(interface_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

/// Take all the pallet attributes (e.g. attribute like `#[interface..]`) and decode them to `Attr`
pub fn take_item_interface_attrs<Attr>(item: &mut impl MutItemAttrs) -> syn::Result<Vec<Attr>>
where
	Attr: syn::parse::Parse,
{
	let mut pallet_attrs = Vec::new();

	while let Some(attr) = take_first_item_interface_attr(item)? {
		pallet_attrs.push(attr)
	}

	Ok(pallet_attrs)
}

/// Take the first interface attribute (e.g. attribute like `#[call_entry..]`) and decode it to
/// `Attr`
pub fn take_first_item_call_entry_attr<Attr>(
	item: &mut impl MutItemAttrs,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = item.mut_item_attrs() { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path
			.segments
			.first()
			.map_or(false, |segment| segment.ident == "call_entry")
	}) {
		let interface_attr = attrs.remove(index);
		Ok(Some(syn::parse2(interface_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

/// Take the first interface attribute (e.g. attribute like `#[view_entry..]`) and decode it to
/// `Attr`
pub fn take_first_item_view_entry_attr<Attr>(
	item: &mut impl MutItemAttrs,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = item.mut_item_attrs() { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path
			.segments
			.first()
			.map_or(false, |segment| segment.ident == "view_entry")
	}) {
		let interface_attr = attrs.remove(index);
		Ok(Some(syn::parse2(interface_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}

impl MutItemAttrs for syn::Item {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		match self {
			Self::Const(item) => Some(item.attrs.as_mut()),
			Self::Enum(item) => Some(item.attrs.as_mut()),
			Self::ExternCrate(item) => Some(item.attrs.as_mut()),
			Self::Fn(item) => Some(item.attrs.as_mut()),
			Self::ForeignMod(item) => Some(item.attrs.as_mut()),
			Self::Impl(item) => Some(item.attrs.as_mut()),
			Self::Macro(item) => Some(item.attrs.as_mut()),
			Self::Macro2(item) => Some(item.attrs.as_mut()),
			Self::Mod(item) => Some(item.attrs.as_mut()),
			Self::Static(item) => Some(item.attrs.as_mut()),
			Self::Struct(item) => Some(item.attrs.as_mut()),
			Self::Trait(item) => Some(item.attrs.as_mut()),
			Self::TraitAlias(item) => Some(item.attrs.as_mut()),
			Self::Type(item) => Some(item.attrs.as_mut()),
			Self::Union(item) => Some(item.attrs.as_mut()),
			Self::Use(item) => Some(item.attrs.as_mut()),
			_ => None,
		}
	}
}

impl MutItemAttrs for syn::TraitItem {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		match self {
			Self::Const(item) => Some(item.attrs.as_mut()),
			Self::Method(item) => Some(item.attrs.as_mut()),
			Self::Type(item) => Some(item.attrs.as_mut()),
			Self::Macro(item) => Some(item.attrs.as_mut()),
			_ => None,
		}
	}
}

impl MutItemAttrs for Vec<syn::Attribute> {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		Some(self)
	}
}

impl MutItemAttrs for syn::ItemTrait {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		Some(&mut self.attrs)
	}
}

impl MutItemAttrs for syn::ItemMod {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		Some(&mut self.attrs)
	}
}

impl MutItemAttrs for syn::ImplItemMethod {
	fn mut_item_attrs(&mut self) -> Option<&mut Vec<syn::Attribute>> {
		Some(&mut self.attrs)
	}
}
