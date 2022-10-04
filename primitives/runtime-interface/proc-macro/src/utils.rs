// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Util function used by this crate.

use proc_macro2::{Span, TokenStream};

use syn::{
	parse_quote, spanned::Spanned, token, Attribute, Error, FnArg, Ident, ItemTrait, Lit, Meta,
	NestedMeta, Pat, PatType, Result, Signature, TraitItem, TraitItemMethod, Type,
};

use proc_macro_crate::{crate_name, FoundCrate};

use std::{
	collections::{btree_map::Entry, BTreeMap},
	env,
};

use quote::quote;

use inflector::Inflector;

/// Runtime interface function with all associated versions of this function.
pub struct RuntimeInterfaceFunction<'a> {
	latest_version: u32,
	versions: BTreeMap<u32, &'a TraitItemMethod>,
}

impl<'a> RuntimeInterfaceFunction<'a> {
	fn new(version: u32, trait_item: &'a TraitItemMethod) -> Self {
		Self {
			latest_version: version,
			versions: {
				let mut res = BTreeMap::new();
				res.insert(version, trait_item);
				res
			},
		}
	}

	pub fn latest_version(&self) -> (u32, &TraitItemMethod) {
		(
			self.latest_version,
			self.versions.get(&self.latest_version).expect(
				"If latest_version has a value, the key with this value is in the versions; qed",
			),
		)
	}
}

/// All functions of a runtime interface grouped by the function names.
pub struct RuntimeInterface<'a> {
	items: BTreeMap<syn::Ident, RuntimeInterfaceFunction<'a>>,
}

impl<'a> RuntimeInterface<'a> {
	pub fn latest_versions(&self) -> impl Iterator<Item = (u32, &TraitItemMethod)> {
		self.items.iter().map(|(_, item)| item.latest_version())
	}

	pub fn all_versions(&self) -> impl Iterator<Item = (u32, &TraitItemMethod)> {
		self.items
			.iter()
			.flat_map(|(_, item)| item.versions.iter())
			.map(|(v, i)| (*v, *i))
	}
}

/// Generates the include for the runtime-interface crate.
pub fn generate_runtime_interface_include() -> TokenStream {
	match crate_name("sp-runtime-interface") {
		Ok(FoundCrate::Itself) => quote!(),
		Ok(FoundCrate::Name(crate_name)) => {
			let crate_name = Ident::new(&crate_name, Span::call_site());
			quote!(
				#[doc(hidden)]
				extern crate #crate_name as proc_macro_runtime_interface;
			)
		},
		Err(e) => {
			let err = Error::new(Span::call_site(), e).to_compile_error();
			quote!( #err )
		},
	}
}

/// Generates the access to the `sp-runtime-interface` crate.
pub fn generate_crate_access() -> TokenStream {
	if env::var("CARGO_PKG_NAME").unwrap() == "sp-runtime-interface" {
		quote!(sp_runtime_interface)
	} else {
		quote!(proc_macro_runtime_interface)
	}
}

/// Create the exchangeable host function identifier for the given function name.
pub fn create_exchangeable_host_function_ident(name: &Ident) -> Ident {
	Ident::new(&format!("host_{}", name), Span::call_site())
}

/// Create the host function identifier for the given function name.
pub fn create_host_function_ident(name: &Ident, version: u32, trait_name: &Ident) -> Ident {
	Ident::new(
		&format!("ext_{}_{}_version_{}", trait_name.to_string().to_snake_case(), name, version),
		Span::call_site(),
	)
}

/// Create the host function identifier for the given function name.
pub fn create_function_ident_with_version(name: &Ident, version: u32) -> Ident {
	Ident::new(&format!("{}_version_{}", name, version), Span::call_site())
}

/// Returns the function arguments of the given `Signature`, minus any `self` arguments.
pub fn get_function_arguments<'a>(sig: &'a Signature) -> impl Iterator<Item = PatType> + 'a {
	sig.inputs
		.iter()
		.filter_map(|a| match a {
			FnArg::Receiver(_) => None,
			FnArg::Typed(pat_type) => Some(pat_type),
		})
		.enumerate()
		.map(|(i, arg)| {
			let mut res = arg.clone();
			if let Pat::Wild(wild) = &*arg.pat {
				let ident =
					Ident::new(&format!("__runtime_interface_generated_{}_", i), wild.span());

				res.pat = Box::new(parse_quote!( #ident ))
			}

			res
		})
}

/// Returns the function argument names of the given `Signature`, minus any `self`.
pub fn get_function_argument_names<'a>(sig: &'a Signature) -> impl Iterator<Item = Box<Pat>> + 'a {
	get_function_arguments(sig).map(|pt| pt.pat)
}

/// Returns the function argument types of the given `Signature`, minus any `Self` type.
pub fn get_function_argument_types<'a>(sig: &'a Signature) -> impl Iterator<Item = Box<Type>> + 'a {
	get_function_arguments(sig).map(|pt| pt.ty)
}

/// Returns the function argument types, minus any `Self` type. If any of the arguments
/// is a reference, the underlying type without the ref is returned.
pub fn get_function_argument_types_without_ref<'a>(
	sig: &'a Signature,
) -> impl Iterator<Item = Box<Type>> + 'a {
	get_function_arguments(sig).map(|pt| pt.ty).map(|ty| match *ty {
		Type::Reference(type_ref) => type_ref.elem,
		_ => ty,
	})
}

/// Returns the function argument names and types, minus any `self`. If any of the arguments
/// is a reference, the underlying type without the ref is returned.
pub fn get_function_argument_names_and_types_without_ref<'a>(
	sig: &'a Signature,
) -> impl Iterator<Item = (Box<Pat>, Box<Type>)> + 'a {
	get_function_arguments(sig).map(|pt| match *pt.ty {
		Type::Reference(type_ref) => (pt.pat, type_ref.elem),
		_ => (pt.pat, pt.ty),
	})
}

/// Returns the `&`/`&mut` for all function argument types, minus the `self` arg. If a function
/// argument is not a reference, `None` is returned.
pub fn get_function_argument_types_ref_and_mut<'a>(
	sig: &'a Signature,
) -> impl Iterator<Item = Option<(token::And, Option<token::Mut>)>> + 'a {
	get_function_arguments(sig).map(|pt| pt.ty).map(|ty| match *ty {
		Type::Reference(type_ref) => Some((type_ref.and_token, type_ref.mutability)),
		_ => None,
	})
}

/// Returns an iterator over all trait methods for the given trait definition.
fn get_trait_methods<'a>(trait_def: &'a ItemTrait) -> impl Iterator<Item = &'a TraitItemMethod> {
	trait_def.items.iter().filter_map(|i| match i {
		TraitItem::Method(ref method) => Some(method),
		_ => None,
	})
}

/// Parse version attribute.
///
/// Returns error if it is in incorrent format. Correct format is only `#[version(X)]`.
fn parse_version_attribute(version: &Attribute) -> Result<u32> {
	let meta = version.parse_meta()?;

	let err = Err(Error::new(
		meta.span(),
		"Unexpected `version` attribute. The supported format is `#[version(1)]`",
	));

	match meta {
		Meta::List(list) =>
			if list.nested.len() != 1 {
				err
			} else if let Some(NestedMeta::Lit(Lit::Int(i))) = list.nested.first() {
				i.base10_parse()
			} else {
				err
			},
		_ => err,
	}
}

/// Return item version (`#[version(X)]`) attribute, if present.
fn get_item_version(item: &TraitItemMethod) -> Result<Option<u32>> {
	item.attrs
		.iter()
		.find(|attr| attr.path.is_ident("version"))
		.map(|attr| parse_version_attribute(attr))
		.transpose()
}

/// Returns all runtime interface members, with versions.
pub fn get_runtime_interface<'a>(trait_def: &'a ItemTrait) -> Result<RuntimeInterface<'a>> {
	let mut functions: BTreeMap<syn::Ident, RuntimeInterfaceFunction<'a>> = BTreeMap::new();

	for item in get_trait_methods(trait_def) {
		let name = item.sig.ident.clone();
		let version = get_item_version(item)?.unwrap_or(1);

		match functions.entry(name.clone()) {
			Entry::Vacant(entry) => {
				entry.insert(RuntimeInterfaceFunction::new(version, item));
			},
			Entry::Occupied(mut entry) => {
				if let Some(existing_item) = entry.get().versions.get(&version) {
					let mut err = Error::new(item.span(), "Duplicated version attribute");
					err.combine(Error::new(
						existing_item.span(),
						"Previous version with the same number defined here",
					));

					return Err(err)
				}

				let interface_item = entry.get_mut();
				if interface_item.latest_version < version {
					interface_item.latest_version = version;
				}
				interface_item.versions.insert(version, item);
			},
		}
	}

	for function in functions.values() {
		let mut next_expected = 1;
		for (version, item) in function.versions.iter() {
			if next_expected != *version {
				return Err(Error::new(
					item.span(),
					format!(
						"Unexpected version attribute: missing version '{}' for this function",
						next_expected
					),
				))
			}
			next_expected += 1;
		}
	}

	Ok(RuntimeInterface { items: functions })
}
