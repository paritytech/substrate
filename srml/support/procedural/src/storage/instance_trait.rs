// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Implementation of the trait instance and the instance structures implementing it.
//! (For not instantiable traits there is still the inherent instance implemented).

use proc_macro2::{TokenStream, Span};
use quote::quote;
use super::{DeclStorageDefExt, StorageLineTypeDef};

const NUMBER_OF_INSTANCE: usize = 16;
const INHERENT_INSTANCE_NAME: &str = "__InherentHiddenInstance";
pub(crate) const DEFAULT_INSTANTIABLE_TRAIT_NAME: &str = "__GeneratedInstantiable";

// prefix for consts in trait Instance
pub(crate) const PREFIX_FOR: &str = "PREFIX_FOR_";
pub(crate) const HEAD_KEY_FOR: &str = "HEAD_KEY_FOR_";

// Used to generate the const:
// `const $name: &'static str = $value_prefix ++ instance_prefix ++ $value_suffix`
struct InstanceConstDef {
	name: syn::Ident,
	value_prefix: String,
	value_suffix: String,
}

// Used to generate an instance implementation.
struct InstanceDef {
	prefix: String,
	instance_struct: syn::Ident,
	doc: TokenStream,
}

pub fn decl_and_impl(scrate: &TokenStream, def: &DeclStorageDefExt) -> TokenStream {
	let mut impls = TokenStream::new();

	let mut const_defs = vec![];

	for line in def.storage_lines.iter() {
		let storage_prefix = format!("{} {}", def.crate_name, line.name);

		let const_name = syn::Ident::new(
			&format!("{}{}", PREFIX_FOR, line.name.to_string()), proc_macro2::Span::call_site()
		);
		const_defs.push(InstanceConstDef {
			name: const_name,
			value_prefix: String::new(),
			value_suffix: storage_prefix.clone(),
		});

		if let StorageLineTypeDef::LinkedMap(_) = line.storage_type {
			let const_name = syn::Ident::new(
				&format!("{}{}", HEAD_KEY_FOR, line.name.to_string()), proc_macro2::Span::call_site()
			);
			const_defs.push(InstanceConstDef {
				name: const_name,
				value_prefix: "head of ".into(),
				value_suffix: storage_prefix,
			});
		}
	}

	impls.extend(create_instance_trait(&const_defs, def));

	// Implementation of instances.
	if let Some(module_instance) = &def.module_instance {
		let instance_defs = (0..NUMBER_OF_INSTANCE)
			.map(|i| {
				let name = format!("Instance{}", i);
				InstanceDef {
					instance_struct: syn::Ident::new(&name, proc_macro2::Span::call_site()),
					prefix: name,
					doc: quote!(#[doc=r"Module instance"]),
				}
			})
			.chain(
				module_instance.instance_default.as_ref().map(|ident| InstanceDef {
					prefix: String::new(),
					instance_struct: ident.clone(),
					doc: quote!(#[doc=r"Default module instance"]),
				})
			);

		for instance_def in instance_defs {
			impls.extend(create_and_impl_instance_struct(scrate, &instance_def, &const_defs, def));
		}
	}

	// The name of the inherently available instance.
	let inherent_instance = syn::Ident::new(INHERENT_INSTANCE_NAME, Span::call_site());

	// Implementation of inherent instance.
	if let Some(default_instance) = def.module_instance.as_ref()
		.and_then(|i| i.instance_default.as_ref())
	{
		impls.extend(quote! {
			#[doc(hidden)]
			pub type #inherent_instance = #default_instance;
		});
	} else {
		let instance_def = InstanceDef {
			prefix: String::new(),
			instance_struct: inherent_instance,
			doc: quote!(#[doc(hidden)]),
		};
		impls.extend(create_and_impl_instance_struct(scrate, &instance_def, &const_defs, def));
	}

	impls
}

fn create_instance_trait(
	const_defs: &[InstanceConstDef],
	def: &DeclStorageDefExt,
) -> TokenStream {
	let instance_trait = def.module_instance.as_ref().map(|i| i.instance_trait.clone())
		.unwrap_or_else(|| syn::Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, Span::call_site()));

	let mut const_impls = TokenStream::new();
	for const_def in const_defs {
		let const_name = &const_def.name;
		const_impls.extend(quote! {
			const #const_name: &'static str;
		});
	}

	let optional_hide = if def.module_instance.is_some() {
		quote!()
	} else {
		quote!(#[doc(hidden)])
	};

	quote! {
		/// Tag a type as an instance of a module.
		///
		/// Defines storage prefixes, they must be unique.
		#optional_hide
		pub trait #instance_trait: 'static {
			/// The prefix used by any storage entry of an instance.
			const PREFIX: &'static str;
			#const_impls
		}
	}
}

fn create_and_impl_instance_struct(
	scrate: &TokenStream,
	instance_def: &InstanceDef,
	const_defs: &[InstanceConstDef],
	def: &DeclStorageDefExt,
) -> TokenStream {
	let mut const_impls = TokenStream::new();

	for const_def in const_defs {
		let const_value = format!(
			"{}{}{}", const_def.value_prefix, instance_def.prefix, const_def.value_suffix
		);
		let const_name = &const_def.name;

		const_impls.extend(quote! {
			const #const_name: &'static str = #const_value;
		});
	}

	let instance_trait = def.module_instance.as_ref().map(|i| i.instance_trait.clone())
		.unwrap_or_else(|| syn::Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, Span::call_site()));

	let instance_struct = &instance_def.instance_struct;
	let prefix = format!("{}{}", instance_def.prefix, def.crate_name.to_string());
	let doc = &instance_def.doc;

	quote! {
		// Those trait are derived because of wrong bounds for generics
		#[derive(
			Clone, Eq, PartialEq,
			#scrate::codec::Encode,
			#scrate::codec::Decode,
			#scrate::RuntimeDebug,
		)]
		#doc
		pub struct #instance_struct;
		impl #instance_trait for #instance_struct {
			const PREFIX: &'static str = #prefix;
			#const_impls
		}
	}
}
