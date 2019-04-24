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

use srml_support_procedural_tools::syn_ext as ext;
use srml_support_procedural_tools::{ToTokens, Parse, custom_keyword, custom_keyword_impl};

use syn::{Ident, Token};
use syn::token::CustomKeyword;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

mod impls;

pub mod transformation;

/// Parsing usage only
#[derive(Parse, ToTokens, Debug)]
struct StorageDefinition {
	pub hidden_crate: Option<SpecificHiddenCrate>,
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
	pub extra_genesis: Option<AddExtraGenesis>,
	pub extra_genesis_skip_phantom_data_field: Option<ExtraGenesisSkipPhantomDataField>,
}

#[derive(Parse, ToTokens, Debug)]
struct SpecificHiddenCrate {
	pub keyword: ext::CustomToken<SpecificHiddenCrate>,
	pub ident: ext::Parens<Ident>,
}

#[derive(Parse, ToTokens, Debug)]
struct AddExtraGenesis {
	pub extragenesis_keyword: ext::CustomToken<AddExtraGenesis>,
	pub content: ext::Braces<AddExtraGenesisContent>,
}

#[derive(Parse, ToTokens, Debug)]
struct ExtraGenesisSkipPhantomDataField {
	pub genesis_phantom_keyword: ext::CustomToken<ExtraGenesisSkipPhantomDataField>,
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
	pub config_keyword: ext::CustomToken<ConfigKeyword>,
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
	pub getter: Option<DeclStorageGetter>,
	pub config: Option<DeclStorageConfig>,
	pub build: Option<DeclStorageBuild>,
	pub coldot_token: Token![:],
	pub storage_type: DeclStorageType,
	pub default_value: ext::Opt<DeclStorageDefault>,
}


#[derive(Parse, ToTokens, Debug)]
struct DeclStorageGetter {
	pub getter_keyword: ext::CustomToken<DeclStorageGetter>,
	pub getfn: ext::Parens<Ident>,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageConfig {
	pub config_keyword: ext::CustomToken<DeclStorageConfig>,
	pub expr: ext::Parens<Option<syn::Ident>>,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageBuild {
	pub build_keyword: ext::CustomToken<DeclStorageBuild>,
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
	pub map_keyword: ext::CustomToken<MapKeyword>,
	pub hasher: Option<SetHasher>,
	pub key: syn::Type,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageLinkedMap {
	pub map_keyword: ext::CustomToken<LinkedMapKeyword>,
	pub hasher: Option<SetHasher>,
	pub key: syn::Type,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageDoubleMap {
	pub map_keyword: ext::CustomToken<DoubleMapKeyword>,
	pub hasher: Option<SetHasher>,
	pub key1: syn::Type,
	pub comma_keyword: Token![,],
	pub key2_hasher: Hasher,
	pub key2: ext::Parens<syn::Type>,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(Parse, ToTokens, Debug)]
enum Hasher {
	Blake2_256(ext::CustomToken<Blake2_256Keyword>),
	Blake2_128(ext::CustomToken<Blake2_128Keyword>),
	Twox256(ext::CustomToken<Twox256Keyword>),
	Twox128(ext::CustomToken<Twox128Keyword>),
	Twox64Concat(ext::CustomToken<Twox64ConcatKeyword>),
}

#[derive(Parse, ToTokens, Debug)]
struct DeclStorageDefault {
	pub equal_token: Token![=],
	pub expr: syn::Expr,
}

#[derive(Parse, ToTokens, Debug)]
struct SetHasher {
	pub hasher_keyword: ext::CustomToken<SetHasher>,
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

	fn into_hashable_fn(&self) -> TokenStream2 {
		match self {
			HasherKind::Blake2_256 => quote!( blake2_256 ),
			HasherKind::Blake2_128 => quote!( blake2_128 ),
			HasherKind::Twox256 => quote!( twox_256 ),
			HasherKind::Twox128 => quote!( twox_128 ),
			HasherKind::Twox64Concat => quote!( twox_64_concat),
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

custom_keyword_impl!(SpecificHiddenCrate, "hiddencrate", "hiddencrate as keyword");
custom_keyword_impl!(DeclStorageConfig, "config", "build as keyword");
custom_keyword!(ConfigKeyword, "config", "config as keyword");
custom_keyword!(BuildKeyword, "build", "build as keyword");
custom_keyword_impl!(DeclStorageBuild, "build", "storage build config");
custom_keyword_impl!(AddExtraGenesis, "add_extra_genesis", "storage extra genesis");
custom_keyword_impl!(DeclStorageGetter, "get", "storage getter");
custom_keyword!(MapKeyword, "map", "map as keyword");
custom_keyword!(LinkedMapKeyword, "linked_map", "linked_map as keyword");
custom_keyword!(DoubleMapKeyword, "double_map", "double_map as keyword");
custom_keyword!(Blake2_256Keyword, "blake2_256", "Blake2_256 as keyword");
custom_keyword!(Blake2_128Keyword, "blake2_128", "Blake2_128 as keyword");
custom_keyword!(Twox256Keyword, "twox_256", "Twox256 as keyword");
custom_keyword!(Twox128Keyword, "twox_128", "Twox128 as keyword");
custom_keyword!(Twox64ConcatKeyword, "twox_64_concat", "Twox64Concat as keyword");
custom_keyword_impl!(ExtraGenesisSkipPhantomDataField, "extra_genesis_skip_phantom_data_field", "extra_genesis_skip_phantom_data_field as keyword");
custom_keyword_impl!(SetHasher, "hasher", "storage hasher");
