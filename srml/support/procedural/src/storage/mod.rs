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

// mod impls;
mod storage_struct;
mod parse;
mod store_trait;
mod getters;
mod metadata;
mod instance_trait;
mod genesis_config;
// pub mod transformation;

use quote::quote;
use srml_support_procedural_tools::{
	generate_crate_access, generate_hidden_includes, syn_ext as ext
};

pub struct DeclStorageDef {
	hidden_crate: Option<syn::Ident>,
	visibility: syn::Visibility,
	store_trait: syn::Ident,
	module_name: syn::Ident,
	module_runtime_generic: syn::Ident,
	module_runtime_trait: syn::Path,
	module_instance: Option<ModuleInstanceDef>,
	where_clause: Option<syn::WhereClause>,
	extra_genesis_build: Option<syn::Expr>,
	extra_genesis_config_lines: Vec<ExtraGenesisLineDef>,
	storage_lines: Vec<StorageLineDef>,
	crate_name: syn::Ident,
}

impl syn::parse::Parse for DeclStorageDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		parse::parse(input)
	}
}

// Extended version of `DeclStorageDef` with useful precomputed value.
pub struct DeclStorageDefExt {
	hidden_crate: Option<syn::Ident>,
	visibility: syn::Visibility,
	store_trait: syn::Ident,
	#[allow(unused)]
	module_name: syn::Ident,
	module_runtime_generic: syn::Ident,
	module_runtime_trait: syn::Path,
	module_instance: Option<ModuleInstanceDef>,
	where_clause: Option<syn::WhereClause>,
	extra_genesis_build: Option<syn::Expr>,
	extra_genesis_config_lines: Vec<ExtraGenesisLineDef>,
	storage_lines: Vec<StorageLineDefExt>,
	crate_name: syn::Ident,
	module_struct: proc_macro2::TokenStream,
	module_impl: proc_macro2::TokenStream,
	optional_instance: Option<proc_macro2::TokenStream>,
	optional_instance_bound: Option<proc_macro2::TokenStream>,
	optional_instance_bound_optional_default: Option<proc_macro2::TokenStream>,
}

impl From<DeclStorageDef> for DeclStorageDefExt {
	fn from(mut def: DeclStorageDef) -> Self {
		let storage_lines = def.storage_lines.drain(..).collect::<Vec<_>>();
		let storage_lines = storage_lines.into_iter()
			.map(|line| StorageLineDefExt::from_def(line, &def))
			.collect();

		let (
			optional_instance,
			optional_instance_bound,
			optional_instance_bound_optional_default,
		) = if let Some(instance) = def.module_instance.as_ref() {
			let instance_generic = &instance.instance_generic;
			let instance_trait= &instance.instance_trait;
			let optional_equal_instance_default = instance.instance_default.as_ref()
				.map(|d| quote!( = #d ));
			(
				Some(quote!(#instance_generic)),
				Some(quote!(#instance_generic: #instance_trait)),
				Some(quote!(#instance_generic: #instance_trait #optional_equal_instance_default)),
			)
		} else {
			(None, None, None)
		};

		let module_runtime_generic = &def.module_runtime_generic;
		let module_runtime_trait = &def.module_runtime_trait;
		let module_name = &def.module_name;

		let module_struct = quote!(
			#module_name<#module_runtime_generic, #optional_instance>
		);

		let module_impl = quote!(
			<#module_runtime_generic: #module_runtime_trait + 'static, #optional_instance_bound>
		);

		Self {
			hidden_crate: def.hidden_crate,
			visibility: def.visibility,
			store_trait: def.store_trait,
			module_name: def.module_name,
			module_runtime_generic: def.module_runtime_generic,
			module_runtime_trait: def.module_runtime_trait,
			module_instance: def.module_instance,
			where_clause: def.where_clause,
			extra_genesis_build: def.extra_genesis_build,
			extra_genesis_config_lines: def.extra_genesis_config_lines,
			crate_name: def.crate_name,
			storage_lines,
			module_struct,
			module_impl,
			optional_instance,
			optional_instance_bound,
			optional_instance_bound_optional_default,
		}
	}
}

pub struct ModuleInstanceDef {
	instance_generic: syn::Ident,
	instance_trait: syn::Ident,
	instance_default: Option<syn::Ident>,
}

pub struct StorageLineDef {
	attrs: Vec<syn::Attribute>,
	visibility: syn::Visibility,
	name: syn::Ident,
	getter: Option<syn::Ident>,
	config: Option<syn::Ident>,
	build: Option<syn::Expr>,
	default_value: Option<syn::Expr>,
	storage_type: StorageLineTypeDef,
}

pub struct StorageLineDefExt {
	#[allow(unused)]
	attrs: Vec<syn::Attribute>,
	visibility: syn::Visibility,
	name: syn::Ident,
	getter: Option<syn::Ident>,
	config: Option<syn::Ident>,
	build: Option<syn::Expr>,
	default_value: Option<syn::Expr>,
	storage_type: StorageLineTypeDef,
	doc_attrs: Vec<syn::Meta>,
	query_type: syn::Type,
	value_type: syn::Type,
	storage_struct: proc_macro2::TokenStream,
	optional_storage_runtime_comma: Option<proc_macro2::TokenStream>,
	optional_storage_runtime_bound_comma: Option<proc_macro2::TokenStream>,
	optional_storage_where_clause: Option<proc_macro2::TokenStream>,
	storage_trait: proc_macro2::TokenStream,
	storage_generator_trait: proc_macro2::TokenStream,
	#[allow(unused)]
	is_generic_over_runtime: bool,
	is_option: bool,
}

impl StorageLineDefExt {
	fn from_def(storage_def: StorageLineDef, def: &DeclStorageDef) -> Self {
		let is_generic_over_runtime = match &storage_def.storage_type {
			StorageLineTypeDef::Simple(value) => {
				ext::type_contains_ident(&value, &def.module_runtime_generic)
			},
			StorageLineTypeDef::Map(map) => {
				ext::type_contains_ident(&map.key, &def.module_runtime_generic)
					|| ext::type_contains_ident(&map.value, &def.module_runtime_generic)
			}
			StorageLineTypeDef::LinkedMap(map) => {
				ext::type_contains_ident(&map.key, &def.module_runtime_generic)
					|| ext::type_contains_ident(&map.value, &def.module_runtime_generic)
			}
			StorageLineTypeDef::DoubleMap(map) => {
				ext::type_contains_ident(&map.key1, &def.module_runtime_generic)
					|| ext::type_contains_ident(&map.key2, &def.module_runtime_generic)
					|| ext::type_contains_ident(&map.value, &def.module_runtime_generic)
			}
		};

		let query_type = match &storage_def.storage_type {
			StorageLineTypeDef::Simple(value) => value.clone(),
			StorageLineTypeDef::Map(map) => map.value.clone(),
			StorageLineTypeDef::LinkedMap(map) => map.value.clone(),
			StorageLineTypeDef::DoubleMap(map) => map.value.clone(),
		};
		let is_option = ext::extract_type_option(&query_type).is_some();
		let value_type = ext::extract_type_option(&query_type).unwrap_or(query_type.clone());

		let module_runtime_generic = &def.module_runtime_generic;
		let module_runtime_trait = &def.module_runtime_trait;
		let optional_storage_runtime_comma = if is_generic_over_runtime {
			Some(quote!( #module_runtime_generic, ))
		} else {
			None
		};
		let optional_storage_runtime_bound_comma = if is_generic_over_runtime {
			Some(quote!( #module_runtime_generic: #module_runtime_trait, ))
		} else {
			None
		};

		let storage_name = &storage_def.name;
		let optional_instance_generic = def.module_instance.as_ref().map(|i| {
			let instance_generic = &i.instance_generic;
			quote!( #instance_generic )
		});
		let storage_struct = quote!(
			#storage_name<#optional_storage_runtime_comma #optional_instance_generic>
		);

		let optional_storage_where_clause = if is_generic_over_runtime {
			def.where_clause.as_ref().map(|w| quote!( #w ))
		} else {
			None
		};

		let storage_trait_trunkated = match &storage_def.storage_type {
			StorageLineTypeDef::Simple(_) => {
				quote!( StorageValue<#value_type> )
			},
			StorageLineTypeDef::Map(map) => {
				let key = &map.key;
				quote!( StorageMap<#key, #value_type> )
			},
			StorageLineTypeDef::LinkedMap(map) => {
				let key = &map.key;
				quote!( StorageLinkedMap<#key, #value_type> )
			},
			StorageLineTypeDef::DoubleMap(map) => {
				let key1 = &map.key1;
				let key2 = &map.key2;
				quote!( StorageDoubleMap<#key1, #key2, #value_type> )
			},
		};

		let storage_trait = quote!( storage::#storage_trait_trunkated );
		let storage_generator_trait = quote!( storage::generator::#storage_trait_trunkated );

		let doc_attrs = storage_def.attrs.iter()
			.filter_map(|a| a.parse_meta().ok())
			.filter(|m| m.name() == "doc")
			.collect();

		Self {
			attrs: storage_def.attrs,
			visibility: storage_def.visibility,
			name: storage_def.name,
			getter: storage_def.getter,
			config: storage_def.config,
			build: storage_def.build,
			default_value: storage_def.default_value,
			storage_type: storage_def.storage_type,
			doc_attrs,
			query_type,
			value_type,
			storage_struct,
			optional_storage_runtime_comma,
			optional_storage_runtime_bound_comma,
			optional_storage_where_clause,
			storage_trait,
			storage_generator_trait,
			is_generic_over_runtime,
			is_option,
		}
	}
}

pub enum StorageLineTypeDef {
	Map(MapDef),
	LinkedMap(MapDef),
	DoubleMap(DoubleMapDef),
	Simple(syn::Type),
}

pub struct MapDef {
	pub hasher: HasherKind,
	pub key: syn::Type,
	pub value: syn::Type,
}

pub struct DoubleMapDef {
	pub hasher1: HasherKind,
	pub hasher2: HasherKind,
	pub key1: syn::Type,
	pub key2: syn::Type,
	pub value: syn::Type,
}

pub struct ExtraGenesisLineDef {
	attrs: Vec<syn::Attribute>,
	name: syn::Ident,
	typ: syn::Type,
	default: Option<syn::Expr>,
}

#[derive(Debug, Clone)]
pub enum HasherKind {
	Blake2_256,
	Blake2_128,
	Twox256,
	Twox128,
	Twox64Concat,
}

impl HasherKind {
	fn to_storage_hasher_struct(&self) -> proc_macro2::TokenStream {
		match self {
			HasherKind::Blake2_256 => quote!( Blake2_256 ),
			HasherKind::Blake2_128 => quote!( Blake2_128 ),
			HasherKind::Twox256 => quote!( Twox256 ),
			HasherKind::Twox128 => quote!( Twox128 ),
			HasherKind::Twox64Concat => quote!( Twox64Concat ),
		}
	}

	fn into_metadata(&self) -> proc_macro2::TokenStream {
		match self {
			HasherKind::Blake2_256 => quote!( StorageHasher::Blake2_256 ),
			HasherKind::Blake2_128 => quote!( StorageHasher::Blake2_128 ),
			HasherKind::Twox256 => quote!( StorageHasher::Twox256 ),
			HasherKind::Twox128 => quote!( StorageHasher::Twox128 ),
			HasherKind::Twox64Concat => quote!( StorageHasher::Twox64Concat ),
		}
	}
}

pub fn decl_storage_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let def = syn::parse_macro_input!(input as DeclStorageDef);
	let def_ext = DeclStorageDefExt::from(def);

	let hidden_crate_name = def_ext.hidden_crate.as_ref().map(|i| i.to_string())
		.unwrap_or_else(|| "decl_storage".to_string());

	let scrate = generate_crate_access(&hidden_crate_name, "srml-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "srml-support");

	let store_trait = store_trait::decl_and_impl(&def_ext);
	let getters = getters::impl_getters(&scrate, &def_ext);
	let metadata = metadata::impl_metadata(&scrate, &def_ext);
	let instance_trait = instance_trait::decl_and_impl(&scrate, &def_ext);
	let genesis_config = genesis_config::genesis_config_and_build_storage(&scrate, &def_ext);
	let storage_struct = storage_struct::decl_and_impl(&scrate, &def_ext);

	quote!(
		use #scrate::{
			StorageValue as _,
			StorageMap as _,
			StorageLinkedMap as _,
			StorageDoubleMap as _
		};

		#scrate_decl
		#store_trait
		#getters
		#metadata
		#instance_trait
		#genesis_config
		#storage_struct
	).into()
}
