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
//! Proc macro of Support code for the runtime.
// end::description[]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]


extern crate proc_macro;
extern crate proc_macro2;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

#[macro_use]
extern crate srml_support_procedural_tools;

#[cfg(feature = "std")]
extern crate serde;

#[doc(hidden)]
extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
#[doc(hidden)]
extern crate sr_primitives as runtime_primitives;
extern crate substrate_metadata;

extern crate mashup;


#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;
#[cfg(test)]
#[macro_use]
extern crate serde_derive;
#[cfg(test)]
#[macro_use]
extern crate parity_codec_derive;

mod ext;

use proc_macro::TokenStream;


use syn::{Attribute, Ident};
use syn::parse::{Parse, ParseStream, Result};
use syn::token::{CustomKeyword};


#[proc_macro]
pub fn decl_storage2(input: TokenStream) -> TokenStream {
  let def = parse_macro_input!(input as StorageDefinition);
//  panic!("{:?}", &def);

  // old macro naming convention (s replaces $)
  let StorageDefinition {
    visibility: spub,
    ident: sstoretype,
    module_ident: smodulename,
    mod_param: strait,
    crate_ident: scratename,
    content: ext::Braces { content: st, ..},
    ..
  } = def;
  if let syn::GenericParam::Type(syn::TypeParam {
    ident: straitinstance,
    bounds: straittypes,
    ..
  }) = strait {
    let straittype = straittypes.first().expect("a trait bound expected").into_value();
      //__decl_storage_items!($cratename $traittype $traitinstance $(#st)*);
    let expanded = quote!{
      __decl_storage_items!(#scratename #straittype #straitinstance #st);
      #spub trait #sstoretype {
        __decl_store_items!(#st);
      }
      impl<#straitinstance: #straittype> #sstoretype for #smodulename<#straitinstance> {
        __impl_store_items!(#straitinstance #st);
      }
      impl<#straitinstance: #straittype> #smodulename<#straitinstance> {
        __impl_store_fns!(#straitinstance #st);
        __impl_store_metadata!(#scratename; #st);
      }

      // TODO generic 

    };

    expanded.into()
    // TokenStream::new()
  } else {
    panic!("Missing declare store generic params");
  }

}


#[derive(ParseStruct, ToTokensStruct, Debug)]
struct StorageDefinition {
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
	 //	$($t:tt)*
   pub content: ext::Braces<ext::StopParse>,
   pub extra_genesis: Option<AddExtraGenesis>,
}


/*		add_extra_genesis {
			$( $(#[$attr:meta])* config($extrafield:ident) : $extraty:ty $(= $default:expr)* ;)*
			build($call:expr);
		}*/
#[derive(ParseStruct, ToTokensStruct, Debug)]
struct AddExtraGenesis {
  pub extragenesis_keyword: ext::CustomToken<AddExtraGenesis>,
  pub content: ext::Braces<AddExtraGenesisContent>,
}

impl CustomKeyword for AddExtraGenesis {
  fn ident() -> &'static str { "add_extra_genesis" }
  fn display() -> &'static str { "storage extra genesis" }
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

macro_rules! custom_keyword {
    ($name:ident, $keyident:expr, $keydisp:expr) => {
 
  #[derive(Debug)]
  struct $name;

  impl CustomKeyword for $name {
    fn ident() -> &'static str { $keyident }
    fn display() -> &'static str { $keydisp }
  }

}}
custom_keyword!(ConfigKeyword, "config", "config as keyword"); 
custom_keyword!(BuildKeyword, "build", "build as keyword"); 

