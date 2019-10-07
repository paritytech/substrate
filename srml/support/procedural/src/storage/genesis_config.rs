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

use srml_support_procedural_tools::syn_ext as ext;
use proc_macro2::{TokenStream, Span};
use syn::{spanned::Spanned, parse_quote};
use quote::{quote, quote_spanned};
use super::{
	DeclStorageDefExt, StorageLineTypeDef,
	instance_trait::DEFAULT_INSTANTIABLE_TRAIT_NAME,
};

const DEFAULT_INSTANCE_NAME: &str = "__GeneratedInstance";

struct GenesisConfigFieldDef {
	doc: Vec<syn::Meta>,
	name: syn::Ident,
	typ: syn::Type,
	default: TokenStream,
}

struct GenesisConfigDef {
	is_generic: bool,
	fields: Vec<GenesisConfigFieldDef>,
	genesis_struct_decl: TokenStream,
	genesis_struct: TokenStream,
	genesis_impl: TokenStream,
	genesis_where_clause: Option<syn::WhereClause>,
}

impl GenesisConfigDef {
	fn from_def(def: &DeclStorageDefExt) -> Self {
		let fields = Self::get_genesis_config_field_defs(def);

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

		Self {
			is_generic,
			fields,
			genesis_struct_decl,
			genesis_struct,
			genesis_impl,
			genesis_where_clause,
		}
	}

	fn get_genesis_config_field_defs(def: &DeclStorageDefExt) -> Vec<GenesisConfigFieldDef> {
		let mut config_field_defs = Vec::new();

		for (config_field, line) in def.storage_lines.iter()
			.filter_map(|line| line.config.as_ref().map(|config_field| (config_field.clone(), line)))
		{
			let value_type = &line.value_type;

			let typ = match &line.storage_type {
				StorageLineTypeDef::Simple(_) => (*value_type).clone(),
				StorageLineTypeDef::Map(map) | StorageLineTypeDef::LinkedMap(map) => {
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
				doc: line.doc_attrs.clone(),
				name: config_field,
				typ,
				default,
			});
		}

		for line in &def.extra_genesis_config_lines {
			let doc = line.attrs.iter()
				.filter_map(|a| a.parse_meta().ok())
				.filter(|m| m.name() == "doc")
				.collect();

			let default = line.default.as_ref().map(|e| quote!( #e ))
				.unwrap_or_else(|| quote!( Default::default() ));


			config_field_defs.push(GenesisConfigFieldDef {
				doc,
				name: line.name.clone(),
				typ: line.typ.clone(),
				default,
			});
		}

		config_field_defs
	}
}

fn decl_genesis_config_and_impl_default(
	scrate: &TokenStream,
	genesis_config: &GenesisConfigDef,
) -> TokenStream {
	let config_fields = genesis_config.fields.iter().map(|field| {
		let (name, typ, doc) = (&field.name, &field.typ, &field.doc);
		quote!( #( #[ #doc] )* pub #name: #typ, )
	});

	let config_field_defaults = genesis_config.fields.iter().map(|field| {
		let (name, default, doc) = (&field.name, &field.default, &field.doc);
		quote!( #( #[ #doc] )* #name: #default, )
	});

	let serde_bug_bound = if !genesis_config.fields.is_empty() {
		let mut b_ser = String::new();
		let mut b_dser = String::new();

		for typ in genesis_config.fields.iter().map(|c| &c.typ) {
			let typ = quote!( #typ );
			b_ser.push_str(&format!("{} : {}::serde::Serialize, ", typ, scrate));
			b_dser.push_str(&format!("{} : {}::serde::de::DeserializeOwned, ", typ, scrate));
		}

		quote! {
			#[serde(bound(serialize = #b_ser))]
			#[serde(bound(deserialize = #b_dser))]
		}
	} else {
		quote!()
	};

	let genesis_struct_decl = &genesis_config.genesis_struct_decl;
	let genesis_struct = &genesis_config.genesis_struct;
	let genesis_impl = &genesis_config.genesis_impl;
	let genesis_where_clause = &genesis_config.genesis_where_clause;

	quote!(
		#[derive(#scrate::Serialize, #scrate::Deserialize)]
		#[cfg(feature = "std")]
		#[serde(rename_all = "camelCase")]
		#[serde(deny_unknown_fields)]
		#serde_bug_bound
		pub struct GenesisConfig#genesis_struct_decl #genesis_where_clause {
			#( #config_fields )*
		}

		#[cfg(feature = "std")]
		impl#genesis_impl Default for GenesisConfig#genesis_struct #genesis_where_clause {
			fn default() -> Self {
				GenesisConfig {
					#( #config_field_defaults )*
				}
			}
		}
	)
}

fn get_inline_builders(
	scrate: &TokenStream,
	def: &DeclStorageDefExt,
) -> Vec<TokenStream> {
	let mut builders = Vec::new();

	for line in def.storage_lines.iter() {
		let storage_struct = &line.storage_struct;
		let storage_trait = &line.storage_trait;
		let value_type = &line.value_type;

		if let Some(builder) = &line.build {
			builders.push(match &line.storage_type {
				StorageLineTypeDef::Simple(_) => {
					quote!{{
						let v: #value_type = (#builder)(&self);
						<#storage_struct as #scrate::#storage_trait>::put::<#value_type>(v);
					}}
				},
				StorageLineTypeDef::Map(map) | StorageLineTypeDef::LinkedMap(map) => {
					let key = &map.key;
					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<
								#key, #value_type
							>(k, v);
						});
					}}
				},
				StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;
					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k1, k2, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<
								#key1, #key2, #value_type
							>(k1, k2, v);
						});
					}}
				},
			});
		} else if let Some(config) = &line.config {
			builders.push(match &line.storage_type {
				StorageLineTypeDef::Simple(_) => {
					quote!{{
						let v = &self.#config;
						<#storage_struct as #scrate::#storage_trait>::put::<&#value_type>(v);
					}}
				},
				StorageLineTypeDef::Map(map)
					| StorageLineTypeDef::LinkedMap(map)
				=> {
					let key = &map.key;
					quote!{{
						let data = &self.#config;
						data.iter().for_each(|(k, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<
								&#key, &#value_type
							>(k, v);
						});
					}}
				},
				StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;
					quote!{{
						let data = &self.#config;
						data.into_iter().for_each(|(k1, k2, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<
								&#key1, &#key2, &#value_type
							>(k1, k2, v);
						});
					}}
				},
			});
		}
	}

	builders
}

/// Return if inline builders or extra genesis builder require generic trait.
// TODO TODO join this with the actual implementation so it is more closer
fn generic_builders(def: &DeclStorageDefExt) -> bool {
	let generic_extra = def.extra_genesis_build.as_ref()
		.map(|expr| ext::expr_contains_ident(&expr, &def.module_runtime_generic))
		.unwrap_or(false);

	let generic_inline = def.storage_lines.iter()
		.filter_map(|line| line.build.as_ref().map(|build| (line, build)))
		.any(|(line, expr)| {
			line.is_generic || ext::expr_contains_ident(&expr, &def.module_runtime_generic)
		});

	generic_extra || generic_inline
}

fn impl_build_storage(
	scrate: &TokenStream,
	def: &DeclStorageDefExt,
	genesis_config: &GenesisConfigDef,
	inline_builders: Vec<TokenStream>,
	extra_genesis_builder: Option<TokenStream>,
) -> TokenStream {
	let runtime_generic = &def.module_runtime_generic;
	let runtime_trait = &def.module_runtime_trait;
	let optional_instance = &def.optional_instance;
	let optional_instance_bound = &def.optional_instance_bound;
	let where_clause = &def.where_clause;

	let inherent_instance = def.optional_instance.clone().unwrap_or_else(|| {
		let name = syn::Ident::new(DEFAULT_INSTANCE_NAME, Span::call_site());
		quote!( #name )
	});
	let inherent_instance_bound = def.optional_instance_bound.clone().unwrap_or_else(|| {
		let bound = syn::Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, Span::call_site());
		quote!( #inherent_instance: #bound )
	});

	let build_storage_impl = quote!(
		<#runtime_generic: #runtime_trait, #inherent_instance_bound>
	);

	let genesis_struct = &genesis_config.genesis_struct;
	let genesis_impl = &genesis_config.genesis_impl;
	let genesis_where_clause = &genesis_config.genesis_where_clause;

	let (
		fn_generic,
		fn_traitinstance,
		fn_where_clause
	) = if !genesis_config.is_generic && generic_builders(def) {
		(
			quote!( <#runtime_generic: #runtime_trait, #optional_instance_bound> ),
			quote!( #runtime_generic, #optional_instance ),
			Some(&def.where_clause),
		)
	} else {
		(quote!(), quote!(), None)
	};

	let build_storage_impl_trait = quote!(
		#scrate::sr_primitives::BuildModuleGenesisStorage<#runtime_generic, #inherent_instance>
	);

	quote!{
		#[cfg(feature = "std")]
		impl#genesis_impl GenesisConfig#genesis_struct #genesis_where_clause {
			pub fn build_storage #fn_generic (self) -> std::result::Result<
				(
					#scrate::sr_primitives::StorageOverlay,
					#scrate::sr_primitives::ChildrenStorageOverlay,
				),
				String
			> #fn_where_clause {
				let mut storage = (Default::default(), Default::default());
				self.assimilate_storage::<#fn_traitinstance>(&mut storage)?;
				Ok(storage)
			}

			/// Assimilate the storage for this module into pre-existing overlays.
			pub fn assimilate_storage #fn_generic (
				self,
				tuple_storage: &mut (
					#scrate::sr_primitives::StorageOverlay,
					#scrate::sr_primitives::ChildrenStorageOverlay,
				),
			) -> std::result::Result<(), String> #fn_where_clause {
				#scrate::with_storage(tuple_storage, || {
					#( #inline_builders )*
					#extra_genesis_builder
					Ok(())
				})
			}
		}

		#[cfg(feature = "std")]
		impl#build_storage_impl #build_storage_impl_trait for GenesisConfig#genesis_struct
			#where_clause
		{
			fn build_module_genesis_storage(
				self,
				storage: &mut (
					#scrate::sr_primitives::StorageOverlay,
					#scrate::sr_primitives::ChildrenStorageOverlay,
				),
			) -> std::result::Result<(), String> {
				self.assimilate_storage::<#fn_traitinstance> (storage)
			}
		}
	}
}

pub fn genesis_config_and_build_storage(
	scrate: &TokenStream,
	def: &DeclStorageDefExt,
) -> TokenStream {
	let inline_builders = get_inline_builders(scrate, def);

	let extra_genesis_builder = def.extra_genesis_build.as_ref().map(|expr| {
		quote_spanned! { expr.span() =>
			let extra_genesis_builder: fn(&Self) = #expr;
			extra_genesis_builder(&self);
		}
	});

	if extra_genesis_builder.is_some() || !inline_builders.is_empty() {
		let genesis_config = &GenesisConfigDef::from_def(def);
		let decl_genesis_config_and_impl_default =
			decl_genesis_config_and_impl_default(scrate, genesis_config);
		let impl_build_storage =
			impl_build_storage(scrate, def, genesis_config, inline_builders, extra_genesis_builder);

		quote!{
			#decl_genesis_config_and_impl_default
			#impl_build_storage
		}
	} else {
		quote!()
	}
}
