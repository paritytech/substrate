// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Genesis config definition.

use frame_support_procedural_tools::syn_ext as ext;
use proc_macro2::TokenStream;
use syn::{spanned::Spanned, parse_quote};
use quote::quote;
use super::super::{DeclStorageDefExt, StorageLineTypeDef};

pub struct GenesisConfigFieldDef {
	pub name: syn::Ident,
	pub typ: syn::Type,
	pub attrs: Vec<syn::Meta>,
	pub default: TokenStream,
}

pub struct GenesisConfigDef {
	pub is_generic: bool,
	pub fields: Vec<GenesisConfigFieldDef>,
	/// For example: `<T: Trait<I>, I: Instance=DefaultInstance>`.
	pub genesis_struct_decl: TokenStream,
	/// For example: `<T, I>`.
	pub genesis_struct: TokenStream,
	/// For example: `<T: Trait<I>, I: Instance>`.
	pub genesis_impl: TokenStream,
	/// The where clause to use to constrain generics if genesis config is generic.
	pub genesis_where_clause: Option<syn::WhereClause>,
}

impl GenesisConfigDef {
	pub fn from_def(def: &DeclStorageDefExt) -> syn::Result<Self> {
		let fields = Self::get_genesis_config_field_defs(def)?;

		let is_generic = fields.iter()
			.any(|field| ext::type_contains_ident(&field.typ, &def.module_runtime_generic));

		let (
			genesis_struct_decl,
			genesis_impl,
			genesis_struct,
			genesis_where_clause
		) = if is_generic {
			let runtime_generic = &def.module_runtime_generic;
			let runtime_trait = &def.module_runtime_trait;
			let optional_instance = &def.optional_instance;
			let optional_instance_bound = &def.optional_instance_bound;
			let optional_instance_bound_optional_default = &def.optional_instance_bound_optional_default;
			let where_clause = &def.where_clause;
			(
				quote!(<#runtime_generic: #runtime_trait, #optional_instance_bound_optional_default>),
				quote!(<#runtime_generic: #runtime_trait, #optional_instance_bound>),
				quote!(<#runtime_generic, #optional_instance>),
				where_clause.clone(),
			)
		} else {
			(quote!(), quote!(), quote!(), None)
		};

		Ok(Self {
			is_generic,
			fields,
			genesis_struct_decl,
			genesis_struct,
			genesis_impl,
			genesis_where_clause,
		})
	}

	fn get_genesis_config_field_defs(def: &DeclStorageDefExt)
		-> syn::Result<Vec<GenesisConfigFieldDef>>
	{
		let mut config_field_defs = Vec::new();

		for (config_field, line) in def.storage_lines.iter()
			.filter_map(|line| line.config.as_ref().map(|config_field| (config_field.clone(), line)))
		{
			let value_type = &line.value_type;

			let typ = match &line.storage_type {
				StorageLineTypeDef::Simple(_) => (*value_type).clone(),
				StorageLineTypeDef::Map(map) => {
					let key = &map.key;
					parse_quote!( Vec<(#key, #value_type)> )
				},
				StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;

					parse_quote!( Vec<(#key1, #key2, #value_type)> )
				},
			};

			let default = line.default_value.as_ref()
				.map(|d| {
					if line.is_option {
						quote!( #d.unwrap_or_default() )
					} else {
						quote!( #d )
					}
				})
				.unwrap_or_else(|| quote!( Default::default() ));

			config_field_defs.push(GenesisConfigFieldDef {
				name: config_field,
				typ,
				attrs: line.doc_attrs.clone(),
				default,
			});
		}

		for line in &def.extra_genesis_config_lines {
			let attrs = line.attrs.iter()
				.map(|attr| {
					let meta = attr.parse_meta()?;
					if meta.path().is_ident("cfg") {
						return Err(syn::Error::new(
							meta.span(),
							"extra genesis config items do not support `cfg` attribute"
						));
					}
					Ok(meta)
				})
				.collect::<syn::Result<_>>()?;

			let default = line.default.as_ref().map(|e| quote!( #e ))
				.unwrap_or_else(|| quote!( Default::default() ));


			config_field_defs.push(GenesisConfigFieldDef {
				name: line.name.clone(),
				typ: line.typ.clone(),
				attrs,
				default,
			});
		}

		Ok(config_field_defs)
	}
}
