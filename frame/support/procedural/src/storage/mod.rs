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

//! `decl_storage` input definition and expansion.

mod storage_struct;
mod parse;
mod store_trait;
mod getters;
mod metadata;
mod instance_trait;
mod genesis_config;

use quote::quote;
use frame_support_procedural_tools::{
	generate_crate_access, generate_hidden_includes, syn_ext as ext
};

/// All information contained in input of decl_storage
pub struct DeclStorageDef {
	/// Name of the module used to import hidden imports.
	hidden_crate: Option<syn::Ident>,
	/// Visibility of store trait.
	visibility: syn::Visibility,
	/// Name of store trait: usually `Store`.
	store_trait: syn::Ident,
	/// Module name used by construct_runtime: usually `Module`.
	module_name: syn::Ident,
	/// Usually `T`.
	module_runtime_generic: syn::Ident,
	/// Usually `Trait`
	module_runtime_trait: syn::Path,
	/// For instantiable module: usually `I: Instance=DefaultInstance`.
	module_instance: Option<ModuleInstanceDef>,
	/// Where claused used to constrain T and I even more.
	where_clause: Option<syn::WhereClause>,
	/// The extra build function used to build storage at genesis.
	extra_genesis_build: Option<syn::Expr>,
	/// The extra genesis config fields.
	extra_genesis_config_lines: Vec<ExtraGenesisLineDef>,
	/// Definition of storages.
	storage_lines: Vec<StorageLineDef>,
	/// Name of the crate, used for storage prefixes.
	crate_name: syn::Ident,
}

impl syn::parse::Parse for DeclStorageDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		parse::parse(input)
	}
}

/// Extended version of `DeclStorageDef` with useful precomputed value.
pub struct DeclStorageDefExt {
	/// Name of the module used to import hidden imports.
	hidden_crate: Option<syn::Ident>,
	/// Visibility of store trait.
	visibility: syn::Visibility,
	/// Name of store trait: usually `Store`.
	store_trait: syn::Ident,
	/// Module name used by construct_runtime: usually `Module`.
	#[allow(unused)]
	module_name: syn::Ident,
	/// Usually `T`.
	module_runtime_generic: syn::Ident,
	/// Usually `Trait`.
	module_runtime_trait: syn::Path,
	/// For instantiable module: usually `I: Instance=DefaultInstance`.
	module_instance: Option<ModuleInstanceDef>,
	/// Where claused used to constrain T and I even more.
	where_clause: Option<syn::WhereClause>,
	/// The extra build function used to build storage at genesis.
	extra_genesis_build: Option<syn::Expr>,
	/// The extra genesis config fields.
	extra_genesis_config_lines: Vec<ExtraGenesisLineDef>,
	/// Definition of storages.
	storage_lines: Vec<StorageLineDefExt>,
	/// Name of the crate, used for storage prefixes.
	crate_name: syn::Ident,
	/// Full struct expansion: `Module<T, I>`.
	module_struct: proc_macro2::TokenStream,
	/// Impl block for module: `<T: Trait, I: Instance>`.
	module_impl: proc_macro2::TokenStream,
	/// For instantiable: `I`.
	optional_instance: Option<proc_macro2::TokenStream>,
	/// For instantiable: `I: Instance`.
	optional_instance_bound: Option<proc_macro2::TokenStream>,
	/// For instantiable: `I: Instance = DefaultInstance`.
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

/// Usually `I: Instance=DefaultInstance`.
pub struct ModuleInstanceDef {
	/// Usually: `I`.
	instance_generic: syn::Ident,
	/// Usually: `Instance`.
	instance_trait: syn::Ident,
	/// Usually: `DefaultInstance`.
	instance_default: Option<syn::Ident>,
}

pub struct StorageLineDef {
	attrs: Vec<syn::Attribute>,
	/// Visibility of the storage struct.
	visibility: syn::Visibility,
	name: syn::Ident,
	/// The name of getter function to be implemented on Module struct.
	getter: Option<syn::Ident>,
	/// The name of the field to be used in genesis config if any.
	config: Option<syn::Ident>,
	/// The build function of the storage if any.
	build: Option<syn::Expr>,
	/// Default value of genesis config field and also for storage when no value available.
	default_value: Option<syn::Expr>,
	storage_type: StorageLineTypeDef,
}

pub struct StorageLineDefExt {
	#[allow(unused)]
	attrs: Vec<syn::Attribute>,
	/// Visibility of the storage struct.
	visibility: syn::Visibility,
	name: syn::Ident,
	/// The name of getter function to be implemented on Module struct.
	getter: Option<syn::Ident>,
	/// The name of the field to be used in genesis config if any.
	config: Option<syn::Ident>,
	/// The build function of the storage if any.
	build: Option<syn::Expr>,
	/// Default value of genesis config field and also for storage when no value available.
	default_value: Option<syn::Expr>,
	storage_type: StorageLineTypeDef,
	doc_attrs: Vec<syn::Meta>,
	/// Either the type stored in storage or wrapped in an Option.
	query_type: syn::Type,
	/// The type stored in storage.
	value_type: syn::Type,
	/// Full struct, for example: `StorageName<T, I>`.
	storage_struct: proc_macro2::TokenStream,
	/// If storage is generic over runtime then `T`.
	optional_storage_runtime_comma: Option<proc_macro2::TokenStream>,
	/// If storage is generic over runtime then `T: Trait`.
	optional_storage_runtime_bound_comma: Option<proc_macro2::TokenStream>,
	/// The where clause to use to constrain generics if storage is generic over runtime.
	optional_storage_where_clause: Option<proc_macro2::TokenStream>,
	/// Full trait, for example: `storage::StorageMap<u32, u32>`.
	storage_trait: proc_macro2::TokenStream,
	/// Full trait, for example: `storage::generator::StorageMap<u32, u32>`.
	storage_generator_trait: proc_macro2::TokenStream,
	/// Whether the storage is generic.
	is_generic: bool,
	/// Whether the storage value is an option.
	is_option: bool,
}

impl StorageLineDefExt {
	fn from_def(storage_def: StorageLineDef, def: &DeclStorageDef) -> Self {
		let is_generic = match &storage_def.storage_type {
			StorageLineTypeDef::Simple(value) => {
				ext::type_contains_ident(&value, &def.module_runtime_generic)
			},
			StorageLineTypeDef::Map(map) => {
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
			StorageLineTypeDef::DoubleMap(map) => map.value.clone(),
		};
		let is_option = ext::extract_type_option(&query_type).is_some();
		let value_type = ext::extract_type_option(&query_type).unwrap_or(query_type.clone());

		let module_runtime_generic = &def.module_runtime_generic;
		let module_runtime_trait = &def.module_runtime_trait;
		let optional_storage_runtime_comma = if is_generic {
			Some(quote!( #module_runtime_generic, ))
		} else {
			None
		};
		let optional_storage_runtime_bound_comma = if is_generic {
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

		let optional_storage_where_clause = if is_generic {
			def.where_clause.as_ref().map(|w| quote!( #w ))
		} else {
			None
		};

		let storage_trait_truncated = match &storage_def.storage_type {
			StorageLineTypeDef::Simple(_) => {
				quote!( StorageValue<#value_type> )
			},
			StorageLineTypeDef::Map(map) => {
				let key = &map.key;
				quote!( StorageMap<#key, #value_type> )
			},
			StorageLineTypeDef::DoubleMap(map) => {
				let key1 = &map.key1;
				let key2 = &map.key2;
				quote!( StorageDoubleMap<#key1, #key2, #value_type> )
			},
		};

		let storage_trait = quote!( storage::#storage_trait_truncated );
		let storage_generator_trait = quote!( storage::generator::#storage_trait_truncated );

		let doc_attrs = storage_def.attrs.iter()
			.filter_map(|a| a.parse_meta().ok())
			.filter(|m| m.path().is_ident("doc"))
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
			is_generic,
			is_option,
		}
	}
}

pub enum StorageLineTypeDef {
	Map(MapDef),
	DoubleMap(DoubleMapDef),
	Simple(syn::Type),
}

pub struct MapDef {
	pub hasher: HasherKind,
	pub key: syn::Type,
	/// This is the query value not the inner value used in storage trait implementation.
	pub value: syn::Type,
}

pub struct DoubleMapDef {
	pub hasher1: HasherKind,
	pub hasher2: HasherKind,
	pub key1: syn::Type,
	pub key2: syn::Type,
	/// This is the query value not the inner value used in storage trait implementation.
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
	Blake2_128Concat,
	Twox256,
	Twox128,
	Twox64Concat,
	Identity,
}

impl HasherKind {
	fn to_storage_hasher_struct(&self) -> proc_macro2::TokenStream {
		match self {
			HasherKind::Blake2_256 => quote!( Blake2_256 ),
			HasherKind::Blake2_128 => quote!( Blake2_128 ),
			HasherKind::Blake2_128Concat => quote!( Blake2_128Concat ),
			HasherKind::Twox256 => quote!( Twox256 ),
			HasherKind::Twox128 => quote!( Twox128 ),
			HasherKind::Twox64Concat => quote!( Twox64Concat ),
			HasherKind::Identity => quote!( Identity ),
		}
	}

	fn into_metadata(&self) -> proc_macro2::TokenStream {
		match self {
			HasherKind::Blake2_256 => quote!( StorageHasher::Blake2_256 ),
			HasherKind::Blake2_128 => quote!( StorageHasher::Blake2_128 ),
			HasherKind::Blake2_128Concat => quote!( StorageHasher::Blake2_128Concat ),
			HasherKind::Twox256 => quote!( StorageHasher::Twox256 ),
			HasherKind::Twox128 => quote!( StorageHasher::Twox128 ),
			HasherKind::Twox64Concat => quote!( StorageHasher::Twox64Concat ),
			HasherKind::Identity => quote!( StorageHasher::Identity ),
		}
	}
}

/// Full implementation of decl_storage.
pub fn decl_storage_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let def = syn::parse_macro_input!(input as DeclStorageDef);
	let def_ext = DeclStorageDefExt::from(def);

	let hidden_crate_name = def_ext.hidden_crate.as_ref().map(|i| i.to_string())
		.unwrap_or_else(|| "decl_storage".to_string());

	let scrate = generate_crate_access(&hidden_crate_name, "frame-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "frame-support");

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
			StorageDoubleMap as _,
			StoragePrefixedMap as _,
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
