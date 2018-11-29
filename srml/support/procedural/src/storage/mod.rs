// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use syn::Ident;
use syn::token::CustomKeyword;

pub mod transfo;

/// Parsing usage only
#[derive(ParseStruct, ToTokensStruct, Debug)]
struct StorageDefinition {
	pub runtime_crate: Option<SpecificRuntimeCrate>,
	pub visibility: syn::Visibility,
	pub trait_token: Token![trait],
	pub ident: Ident,
	pub for_token: Token![for],
	pub module_ident: Ident,
	pub mod_lt_token: Token![<],
	pub mod_param: syn::GenericParam,
	pub mod_gt_token: Token![>],
	pub as_token: Token![as],
	pub crate_ident: Ident,
	pub content: ext::Braces<ext::Punctuated<DeclStorageLine, Token![;]>>,
	pub extra_genesis: Option<AddExtraGenesis>,
}


#[derive(ParseStruct, ToTokensStruct, Debug)]
struct SpecificRuntimeCrate {
	pub keyword: ext::CustomToken<SpecificRuntimeCrate>,
	pub ident: ext::Parens<syn::Ident>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesis {
	pub extragenesis_keyword: ext::CustomToken<AddExtraGenesis>,
	pub content: ext::Braces<AddExtraGenesisContent>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesisContent {
	pub lines: ext::Punctuated<AddExtraGenesisLineEnum, Token![;]>,
}

#[derive(ParseEnum, ToTokensEnum, Debug)]
enum AddExtraGenesisLineEnum {
	AddExtraGenesisLine(AddExtraGenesisLine),
	AddExtraGenesisBuild(DeclStorageBuild),
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesisLine {
	pub attrs: ext::OuterAttributes,
	pub config_keyword: ext::CustomToken<ConfigKeyword>,
	pub extra_field: ext::Parens<Ident>,
	pub coldot_token: Token![:],
	pub extra_type: syn::Type,
	// TODO use a custom ext::Option instead (syn option on '=' fails)
	pub default_value: ext::Seq<DeclStorageDefault>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
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
	// TODO use a custom ext::Option instead (syn option on '=' fails)
	pub default_value: ext::Seq<DeclStorageDefault>,
}


#[derive(ParseStruct, ToTokensStruct, Debug)]
struct DeclStorageGetter {
	pub getter_keyword: ext::CustomToken<DeclStorageGetter>,
	pub getfn: ext::Parens<Ident>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct DeclStorageConfig {
	pub config_keyword: ext::CustomToken<DeclStorageConfig>,
	pub expr: ext::Parens<Option<syn::Ident>>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct DeclStorageBuild {
	pub build_keyword: ext::CustomToken<DeclStorageBuild>,
	pub expr: ext::Parens<syn::Expr>,
}

#[derive(ParseEnum, ToTokensEnum, Debug)]
enum DeclStorageType {
	Map(DeclStorageMap),
	Simple(syn::Type),
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct DeclStorageMap {
	pub map_keyword: ext::CustomToken<MapKeyword>,
	pub key: syn::Type,
	pub ass_keyword: Token![=>],
	pub value: syn::Type,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct DeclStorageDefault {
	pub equal_token: Token![=],
	pub expr: syn::Expr,
}

custom_keyword_impl!(SpecificRuntimeCrate, "runtimecrate", "runtimecrate as keyword");
custom_keyword_impl!(DeclStorageConfig, "config", "build as keyword");
custom_keyword!(ConfigKeyword, "config", "config as keyword");
custom_keyword!(BuildKeyword, "build", "build as keyword");
custom_keyword_impl!(DeclStorageBuild, "build", "storage build config");
custom_keyword_impl!(AddExtraGenesis, "add_extra_genesis", "storage extra genesis");
custom_keyword_impl!(DeclStorageGetter, "get", "storage getter");
custom_keyword!(MapKeyword, "map", "map as keyword");
