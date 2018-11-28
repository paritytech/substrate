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

// parsing stuff


#[derive(ParseStruct, ToTokensStruct, Debug)]
struct StorageDefinition {
  pub runtime_crate: Option<SpecificRuntimeCrate>,
  // $pub:vis trait $storetype:ident for $modulename:ident<$traitinstance:ident: $traittype:ident> as $cratename:ident
  // TODO attr support ??  pub attrs: Vec<Attribute>,
  pub visibility: syn::Visibility,
  // TODO ?  pub unsafety: Option<Token![unsafe]>,
  // unneeded  pub auto_token: Option<Token![auto]>,
  pub trait_token: Token![trait],
  pub ident: Ident,
  // TODO?  pub generics: Generics,
  /* could be an idea to allow others trait pub colon_token: Option<Token![:]>,
     pub supertraits: Punctuated<TypeParamBound, Token![+]>,
     pub brace_token: token::Brace,
     pub items: Vec<TraitItem>,*/

  pub for_token: Token![for],
  pub module_ident: Ident,
  // pub module_generics: syn::Generics,
  pub mod_lt_token: Token![<],
  // single param only TODO not compatible with option on tokens!!!
  pub mod_param: syn::GenericParam,
  pub mod_gt_token: Token![>],
  //pub mod_where_clause: Option<syn::WhereClause>,

  pub as_token: Token![as],
  pub crate_ident: Ident,
  // $($t:tt)*
  pub content: ext::Braces<ext::StopParse>,
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
  AddExtraGenesisBuild(AddExtraGenesisBuild),
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesisLine {
  pub attrs: ext::OuterAttributes,
  pub config_keyword: ext::CustomToken<ConfigKeyword>,
  pub extra_field: ext::Parens<Ident>,
  pub coldot_token: Token![:],
  pub extra_type: syn::Type,
  // this is probably wrong reading from previous macro ()* use as a shorthand for ()+ TODO ask
  pub default_seq: ext::Seq<AddExtraGenesisLineDefault>,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesisLineDefault {
  pub equal_token: Token![=],
  pub expr: syn::Expr,
}

#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesisBuild {
  pub build_keyword: ext::CustomToken<BuildKeyword>,
  pub expr: ext::Parens<syn::Expr>,
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
  // TODO issue using keyword optional with equal token : TODO make an ext::Option ?
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

// same as genesys build, does it make sense to merge?
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
  //pub eq_keyword: ext::CustomToken<DeclStorageDefault>,
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
//custom_keyword_impl!(DeclStorageDefault, "=", "optional decl storage default");
