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

// tag::description[]
//! `decl_storage` macro
// end::description[]

use srml_support_procedural_tools::{ToTokens, Parse, syn_ext as ext};
use syn::{Ident, Token};
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

mod impls;

pub mod transformation;

mod keyword {
	syn::custom_keyword!(hiddencrate);
	syn::custom_keyword!(add_extra_genesis);
	syn::custom_keyword!(extra_genesis_skip_phantom_data_field);
	syn::custom_keyword!(config);
	syn::custom_keyword!(build);
	syn::custom_keyword!(get);
	syn::custom_keyword!(map);
	syn::custom_keyword!(linked_map);
	syn::custom_keyword!(double_map);
	syn::custom_keyword!(blake2_256);
	syn::custom_keyword!(blake2_128);
	syn::custom_keyword!(twox_256);
	syn::custom_keyword!(twox_128);
	syn::custom_keyword!(twox_64_concat);
	syn::custom_keyword!(hasher);
}

/// Parsing usage only
#[derive(Parse, ToTokens, Debug)]
struct StorageDefinition {
	pub hidden_crate: ext::Opt<SpecificHiddenCrate>,
	pub visibility: syn::Visibility,
	pub trait_token: Token![trait],
	pub ident: Ident,
	pub for_token: Token![for],
	pub module_ident: Ident,
	pub mod_lt_token: Token![<],
	pub mod_param: syn::GenericParam,
	pub mod_instance_param_token: Option<Token![,]>,
	pub mod_instance: Option<syn::Ident>,
	pub mod_instantiable_token: Option<Token![:]>,
	pub mod_instantiable: Option<syn::Ident>,
	pub mod_default_instance_token: Option<Token![=]>,
	pub mod_default_instance: Option<syn::Ident>,
	pub mod_gt_token: Token![>],
	pub as_token: Token![as],
	pub crate_ident: Ident,
	pub content: ext::Braces<ext::Punctuated<DeclStorageLine, Token![;]>>,
	pub extra_genesis: ext::Opt<AddExtraGenesis>,
	pub extra_genesis_skip_phantom_data_field: ext::Opt<ExtraGenesisSkipPhantomDataField>,
}

#[derive(Parse, ToTokens, Debug)]
struct SpecificHiddenCrate {
	pub keyword: keyword::hiddencrate,
	pub ident: ext::Parens<Ident>,
}

#[derive(Parse, ToTokens, Debug)]
struct AddExtraGenesis {
	pub extragenesis_keyword: keyword::add_extra_genesis,
	pub content: ext::Braces<AddExtraGenesisContent>,
}

#[derive(Parse, ToTokens, Debug)]
struct ExtraGenesisSkipPhantomDataField {
	pub genesis_phantom_keyword: keyword::extra_genesis_skip_phantom_data_field,
	pub token: Token![;],
}

#[derive(Parse, ToTokens, Debug)]
struct AddExtraGenesisContent {
	pub lines: ext::Punctuated<AddExtraGenesisLineEnum, Token![;]>,
}

#[derive(Parse, ToTokens, Debug)]
enum AddExtraGenesisLineEnum {
	AddExtraGenesisLine(AddExtraGenesisLine),
	AddExtraGenesisBuild(DeclStorageBuild),
}

#[derive(Parse, ToTokens, Debug)]
struct AddExtraGenesisLine {
	pub attrs: ext::OuterAttributes,
	pub config_keyword: keyword::config,
	pub extra_field: ext::Parens<Ident>,
	pub coldot_token: Token![:],
	pub extra_type: syn::Type,
	pub default_value: ext::Opt<DeclStorageDefault>,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageLine {
	// attrs (main use case is doc)
	pub attrs: ext::OuterAttributes,
	// visibility (no need to make optional
	pub visibility: syn::Visibility,
	// name
	pub name: Ident,
	pub getter: ext::Opt<DeclStorageGetter>,
	pub config: ext::Opt<DeclStorageConfig>,
	pub build: ext::Opt<DeclStorageBuild>,
	pub coldot_token: Token![:],
	pub storage_type: DeclStorageType,
	pub default_value: ext::Opt<DeclStorageDefault>,
}


#[derive(Parse, ToTokens, Debug)]
struct DeclStorageGetter {
	pub getter_keyword: keyword::get,
	pub getfn: ext::Parens<Ident>,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageConfig {
	pub config_keyword: keyword::config,
	pub expr: ext::Parens<Option<syn::Ident>>,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageBuild {
	pub build_keyword: keyword::build,
	pub expr: ext::Parens<syn::Expr>,
}

#[derive(Parse, ToTokens, Debug)]
enum DeclStorageType {
	Map(DeclStorageMap),
	LinkedMap(DeclStorageLinkedMap),
	DoubleMap(DeclStorageDoubleMap),
	Simple(syn::Type),
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageMap {
	pub map_keyword: keyword::map,
	pub hasher: ext::Opt<SetHasher>,
	pub key: syn::Type,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageLinkedMap {
	pub map_keyword: keyword::linked_map,
	pub hasher: ext::Opt<SetHasher>,
	pub key: syn::Type,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageDoubleMap {
	pub map_keyword: keyword::double_map,
	pub hasher: ext::Opt<SetHasher>,
	pub key1: syn::Type,
	pub comma_keyword: Token![,],
	pub key2_hasher: Hasher,
	pub key2: ext::Parens<syn::Type>,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
enum Hasher {
	Blake2_256(keyword::blake2_256),
	Blake2_128(keyword::blake2_128),
	Twox256(keyword::twox_256),
	Twox128(keyword::twox_128),
	Twox64Concat(keyword::twox_64_concat),
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageDefault {
	pub equal_token: Token![=],
	pub expr: syn::Expr,
}

#[derive(Parse, ToTokens, Debug)]
struct SetHasher {
	pub hasher_keyword: keyword::hasher,
	pub inner: ext::Parens<Hasher>,
}

#[derive(Debug, Clone)]
enum HasherKind {
	Blake2_256,
	Blake2_128,
	Twox256,
	Twox128,
	Twox64Concat,
}

impl From<&SetHasher> for HasherKind {
	fn from(set_hasher: &SetHasher) -> Self {
		match set_hasher.inner.content {
			Hasher::Blake2_256(_) => HasherKind::Blake2_256,
			Hasher::Blake2_128(_) => HasherKind::Blake2_128,
			Hasher::Twox256(_) => HasherKind::Twox256,
			Hasher::Twox128(_) => HasherKind::Twox128,
			Hasher::Twox64Concat(_) => HasherKind::Twox64Concat,
		}
	}
}
impl HasherKind {
	fn into_storage_hasher_struct(&self) -> TokenStream2 {
		match self {
			HasherKind::Blake2_256 => quote!( Blake2_256 ),
			HasherKind::Blake2_128 => quote!( Blake2_128 ),
			HasherKind::Twox256 => quote!( Twox256 ),
			HasherKind::Twox128 => quote!( Twox128 ),
			HasherKind::Twox64Concat => quote!( Twox64Concat ),
		}
	}

	fn into_metadata(&self) -> TokenStream2 {
		match self {
			HasherKind::Blake2_256 => quote!( StorageHasher::Blake2_256 ),
			HasherKind::Blake2_128 => quote!( StorageHasher::Blake2_128 ),
			HasherKind::Twox256 => quote!( StorageHasher::Twox256 ),
			HasherKind::Twox128 => quote!( StorageHasher::Twox128 ),
			HasherKind::Twox64Concat => quote!( StorageHasher::Twox64Concat ),
		}
	}
}
