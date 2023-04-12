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

//! Util function used by this crate.

use proc_macro2::{Span, TokenStream};

use syn::{
	parse::Parse, parse_quote, spanned::Spanned, token, Error, FnArg, Ident, ItemTrait, LitInt,
	Pat, PatType, Result, Signature, TraitItem, TraitItemMethod, Type,
};

use proc_macro_crate::{crate_name, FoundCrate};

use std::{
	collections::{btree_map::Entry, BTreeMap},
	env,
};

use quote::quote;

use inflector::Inflector;

mod attributes {
	syn::custom_keyword!(register_only);
}

/// A concrete, specific version of a runtime interface function.
pub struct RuntimeInterfaceFunction {
	item: TraitItemMethod,
	should_trap_on_return: bool,
}

impl std::ops::Deref for RuntimeInterfaceFunction {
	type Target = TraitItemMethod;
	fn deref(&self) -> &Self::Target {
		&self.item
	}
}

impl RuntimeInterfaceFunction {
	fn new(item: &TraitItemMethod) -> Result<Self> {
		let mut item = item.clone();
		let mut should_trap_on_return = false;
		item.attrs.retain(|attr| {
			if attr.path.is_ident("trap_on_return") {
				should_trap_on_return = true;
				false
			} else {
				true
			}
		});

		if should_trap_on_return && !matches!(item.sig.output, syn::ReturnType::Default) {
			return Err(Error::new(
				item.sig.ident.span(),
				"Methods marked as #[trap_on_return] cannot return anything",
			))
		}

		Ok(Self { item, should_trap_on_return })
	}

	pub fn should_trap_on_return(&self) -> bool {
		self.should_trap_on_return
	}
}

/// Runtime interface function with all associated versions of this function.
struct RuntimeInterfaceFunctionSet {
	latest_version_to_call: Option<u32>,
	versions: BTreeMap<u32, RuntimeInterfaceFunction>,
}

impl RuntimeInterfaceFunctionSet {
	fn new(version: VersionAttribute, trait_item: &TraitItemMethod) -> Result<Self> {
		Ok(Self {
			latest_version_to_call: version.is_callable().then(|| version.version),
			versions: BTreeMap::from([(
				version.version,
				RuntimeInterfaceFunction::new(trait_item)?,
			)]),
		})
	}

	/// Returns the latest version of this runtime interface function plus the actual function
	/// implementation.
	///
	/// This isn't required to be the latest version, because a runtime interface function can be
	/// annotated with `register_only` to ensure that the host exposes the host function but it
	/// isn't used when compiling the runtime.
	pub fn latest_version_to_call(&self) -> Option<(u32, &RuntimeInterfaceFunction)> {
		self.latest_version_to_call.map(|v| {
			(
			v,
			self.versions.get(&v).expect(
				"If latest_version_to_call has a value, the key with this value is in the versions; qed",
			),
		)
		})
	}

	/// Add a different version of the function.
	fn add_version(
		&mut self,
		version: VersionAttribute,
		trait_item: &TraitItemMethod,
	) -> Result<()> {
		if let Some(existing_item) = self.versions.get(&version.version) {
			let mut err = Error::new(trait_item.span(), "Duplicated version attribute");
			err.combine(Error::new(
				existing_item.span(),
				"Previous version with the same number defined here",
			));

			return Err(err)
		}

		self.versions
			.insert(version.version, RuntimeInterfaceFunction::new(trait_item)?);
		if self.latest_version_to_call.map_or(true, |v| v < version.version) &&
			version.is_callable()
		{
			self.latest_version_to_call = Some(version.version);
		}

		Ok(())
	}
}

/// All functions of a runtime interface grouped by the function names.
pub struct RuntimeInterface {
	items: BTreeMap<syn::Ident, RuntimeInterfaceFunctionSet>,
}

impl RuntimeInterface {
	/// Returns an iterator over all runtime interface function
	/// [`latest_version_to_call`](RuntimeInterfaceFunctionSet::latest_version).
	pub fn latest_versions_to_call(
		&self,
	) -> impl Iterator<Item = (u32, &RuntimeInterfaceFunction)> {
		self.items.iter().filter_map(|(_, item)| item.latest_version_to_call())
	}

	pub fn all_versions(&self) -> impl Iterator<Item = (u32, &RuntimeInterfaceFunction)> {
		self.items
			.iter()
			.flat_map(|(_, item)| item.versions.iter())
			.map(|(v, i)| (*v, i))
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
pub fn get_function_arguments(sig: &Signature) -> impl Iterator<Item = PatType> + '_ {
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
pub fn get_function_argument_names(sig: &Signature) -> impl Iterator<Item = Box<Pat>> + '_ {
	get_function_arguments(sig).map(|pt| pt.pat)
}

/// Returns the function argument types of the given `Signature`, minus any `Self` type.
pub fn get_function_argument_types(sig: &Signature) -> impl Iterator<Item = Box<Type>> + '_ {
	get_function_arguments(sig).map(|pt| pt.ty)
}

/// Returns the function argument types, minus any `Self` type. If any of the arguments
/// is a reference, the underlying type without the ref is returned.
pub fn get_function_argument_types_without_ref(
	sig: &Signature,
) -> impl Iterator<Item = Box<Type>> + '_ {
	get_function_arguments(sig).map(|pt| pt.ty).map(|ty| match *ty {
		Type::Reference(type_ref) => type_ref.elem,
		_ => ty,
	})
}

/// Returns the function argument names and types, minus any `self`. If any of the arguments
/// is a reference, the underlying type without the ref is returned.
pub fn get_function_argument_names_and_types_without_ref(
	sig: &Signature,
) -> impl Iterator<Item = (Box<Pat>, Box<Type>)> + '_ {
	get_function_arguments(sig).map(|pt| match *pt.ty {
		Type::Reference(type_ref) => (pt.pat, type_ref.elem),
		_ => (pt.pat, pt.ty),
	})
}

/// Returns the `&`/`&mut` for all function argument types, minus the `self` arg. If a function
/// argument is not a reference, `None` is returned.
pub fn get_function_argument_types_ref_and_mut(
	sig: &Signature,
) -> impl Iterator<Item = Option<(token::And, Option<token::Mut>)>> + '_ {
	get_function_arguments(sig).map(|pt| pt.ty).map(|ty| match *ty {
		Type::Reference(type_ref) => Some((type_ref.and_token, type_ref.mutability)),
		_ => None,
	})
}

/// Returns an iterator over all trait methods for the given trait definition.
fn get_trait_methods(trait_def: &ItemTrait) -> impl Iterator<Item = &TraitItemMethod> {
	trait_def.items.iter().filter_map(|i| match i {
		TraitItem::Method(ref method) => Some(method),
		_ => None,
	})
}

/// The version attribute that can be found above a runtime interface function.
///
/// Supports the following formats:
/// - `#[version(1)]`
/// - `#[version(1, register_only)]`
///
/// While this struct is only for parsing the inner parts inside the `()`.
struct VersionAttribute {
	version: u32,
	register_only: Option<attributes::register_only>,
}

impl VersionAttribute {
	/// Is this function version callable?
	fn is_callable(&self) -> bool {
		self.register_only.is_none()
	}
}

impl Default for VersionAttribute {
	fn default() -> Self {
		Self { version: 1, register_only: None }
	}
}

impl Parse for VersionAttribute {
	fn parse(input: syn::parse::ParseStream) -> Result<Self> {
		let version: LitInt = input.parse()?;
		let register_only = if input.peek(token::Comma) {
			let _ = input.parse::<token::Comma>();
			Some(input.parse()?)
		} else {
			if !input.is_empty() {
				return Err(Error::new(input.span(), "Unexpected token, expected `,`."))
			}

			None
		};

		Ok(Self { version: version.base10_parse()?, register_only })
	}
}

/// Return [`VersionAttribute`], if present.
fn get_item_version(item: &TraitItemMethod) -> Result<Option<VersionAttribute>> {
	item.attrs
		.iter()
		.find(|attr| attr.path.is_ident("version"))
		.map(|attr| attr.parse_args())
		.transpose()
}

/// Returns all runtime interface members, with versions.
pub fn get_runtime_interface(trait_def: &ItemTrait) -> Result<RuntimeInterface> {
	let mut functions: BTreeMap<syn::Ident, RuntimeInterfaceFunctionSet> = BTreeMap::new();

	for item in get_trait_methods(trait_def) {
		let name = item.sig.ident.clone();
		let version = get_item_version(item)?.unwrap_or_default();

		if version.version < 1 {
			return Err(Error::new(item.span(), "Version needs to be at least `1`."))
		}

		match functions.entry(name.clone()) {
			Entry::Vacant(entry) => {
				entry.insert(RuntimeInterfaceFunctionSet::new(version, item)?);
			},
			Entry::Occupied(mut entry) => {
				entry.get_mut().add_version(version, item)?;
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
