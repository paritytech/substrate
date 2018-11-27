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
#![recursion_limit="128"]

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
extern crate srml_metadata;

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
pub fn decl_storage(input: TokenStream) -> TokenStream {
  let scrate = if std::env::var("CARGO_PKG_NAME").unwrap() == "srml-support" {
    quote!( crate )
  } else {
    quote!( ::runtime_support )
  };
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
    extra_genesis,
    ..
  } = def;

  // make this as another parsing temporarily (switch one macro a time)
  let toparse = st.inner.clone().into();
  //panic!("{}",quote!{ #storage_lines });
  if let syn::GenericParam::Type(syn::TypeParam {
    ident: straitinstance,
    bounds: straittypes,
    ..
  }) = strait {
    let straittype = straittypes.first().expect("a trait bound expected").into_value();
    // TODO when covers all macro move it as inner field parso of storage definition!! (corrently inner
    // macros need st.
    let storage_lines  = parse_macro_input!(toparse as ext::Punctuated<DeclStorageLine, Token![;]>);

    let (config_field, config_field_default, builders) = {
      let mut config_field = Vec::new();
      let mut config_field_default = Vec::new();
      let mut builders = Vec::new();
      for sline in storage_lines.inner {
        let DeclStorageLine {
          attrs,
          visibility,
          name,
          getter,
          config,
          build,
          storage_type,
          default_value,
          ..
        } = sline;

        let is_simple = if let DeclStorageType::Simple(..) = storage_type { true } else { false };

        let mut opt_build = None; 
        // TODO find a name for this eg // normal
        if getter.is_some() && config.is_some() {
          let ident = if let Some(ident) = config.as_ref().expect("previous condition; qed").expr.content.as_ref() {
            quote!{ #ident }
          } else {
            let ident = &getter.as_ref().expect("previous condition; qed").getfn.content;
            quote!{ #ident }
          };
          let option_extracteed = if let DeclStorageType::Simple(ref st) = storage_type {
            ext::extract_type_option(st)
          } else { None };
          let is_option = option_extracteed.is_some();
          let storage_type = option_extracteed.unwrap_or_else(||quote!{ #storage_type });
          config_field.push(quote!{ pub #ident : #storage_type , });
          opt_build = Some(build.as_ref().map(|b|&b.expr.content).map(|b|quote!{ #b })
            .unwrap_or_else(|| quote!{ (|config: &GenesisConfig<#straitinstance>| config.#ident.clone()) })); 
          let fielddefault = default_value.inner.get(0).as_ref().map(|d|&d.expr).map(|d|
            if is_option {
              quote!{ #d.unwrap_or_default() } 
            } else {
              quote!{ #d } 
            })
          .unwrap_or_else(|| quote!{ Default::default() });
          config_field_default.push(quote!{ #ident : #fielddefault , });
        } else {
          opt_build = build.as_ref().map(|b|&b.expr.content).map(|b|quote!{ #b });
        }

        if let Some(builder) = opt_build {
          if is_simple {
            builders.push(quote!{
            {
              use #scrate::codec::Encode;
              let v = (#builder)(&self);
              r.insert(Self::hash(<#name<#straitinstance>>::key()).to_vec(), v.encode());
            }
            });
          } else {
            builders.push(quote!{
            {
              use #scrate::codec::Encode;
              let data = (#builder)(&self);
              for (k, v) in data.into_iter() {
                r.insert(Self::hash(&<#name<#straitinstance>>::key_for(k)).to_vec(), v.encode());
              }
            }
            });
          }
        }

      }
      (config_field, config_field_default, builders)
    };
    // extra genesis
    let (slines, genesis_extrafields, genesis_extrafields_default, sbuild) = if let Some(eg) = extra_genesis {
      let mut sbuild = None;
      let mut lines = Vec::new();
      let mut extra_lines = Vec::new();
      let mut extra_lines_default = Vec::new();
      for ex_content in eg.content.content.lines.inner {
        match ex_content {
          AddExtraGenesisLineEnum::AddExtraGenesisLine(AddExtraGenesisLine {
            attrs,
            extra_field,
            extra_type,
            default_seq,
            ..
          }) => {
            let extrafield = extra_field.content;
            lines.push(quote!{
              #attrs #extrafield : #extra_type #default_seq ;
            });
            extra_lines.push(quote!{
              #attrs pub #extrafield : #extra_type ,
            });
            let extra_default = default_seq.inner.get(0).map(|d|&d.expr).map(|e|quote!{ #e })
              .unwrap_or_else(|| quote!{ Default::default() });
            extra_lines_default.push(quote!{
              #extrafield : #extra_default ,
            });
          },
          AddExtraGenesisLineEnum::AddExtraGenesisBuild(AddExtraGenesisBuild{expr, ..}) => {
            if sbuild.is_some() { panic!( "Only one build expression allowed for extra genesis" ) }
            sbuild = Some(expr.content);
          },
        }
      }
      (lines, extra_lines, extra_lines_default, sbuild)
    } else {
      (Vec::new(), Vec::new(), Vec::new(), None)
    };


    let is_extra_genesis_needed = sbuild.is_some() || config_field.len() > 0 || genesis_extrafields.len() > 0 || builders.len() > 0;
    let extra_genesis = if is_extra_genesis_needed { 
      let scall = sbuild.map(|sb| quote!{ ( #sb ) }).unwrap_or_else(|| quote!{ ( |_, _, _|{} ) });
      quote!{

        //__decl_genesis_config_items!([#straittype #straitinstance] [] [] [] [#( #slines )* ] [#scall] #st);
      
        #[derive(Serialize, Deserialize)]
        #[cfg(feature = "std")]
        #[serde(rename_all = "camelCase")]
        #[serde(deny_unknown_fields)]
        pub struct GenesisConfig<#straitinstance: #straittype> {
			    #[serde(skip)]
			    pub _genesis_phantom_data: #scrate::storage::generator::PhantomData<#straitinstance>,
          #( #config_field )*
          #( #genesis_extrafields )*
        }

        #[cfg(feature = "std")]
        impl<#straitinstance: #straittype> Default for GenesisConfig<#straitinstance> {
          fn default() -> Self {
            GenesisConfig {
					    _genesis_phantom_data: Default::default(),
              #( #config_field_default )*
              #( #genesis_extrafields_default )*
            }
          }
        }

        #[cfg(feature = "std")]
        impl<#straitinstance: #straittype> #scrate::runtime_primitives::BuildStorage for GenesisConfig<#straitinstance>
        {

          fn build_storage(self) -> ::std::result::Result<(#scrate::runtime_primitives::StorageMap, #scrate::runtime_primitives::ChildrenStorageMap), String> {
            let mut r: #scrate::runtime_primitives::StorageMap = Default::default();
				    let mut c: #scrate::runtime_primitives::ChildrenStorageMap = Default::default();


            #( #builders )*

            // extra call
            #scall(&mut r, &mut c, &self);

            Ok((r, c))
          }
        }
      } 
    } else { quote!{} };

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

      #extra_genesis

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
  // $($t:tt)*
  pub content: ext::Braces<ext::StopParse>,
  pub extra_genesis: Option<AddExtraGenesis>,
}


  /*    add_extra_genesis {
        $( $(#[$attr:meta])* config($extrafield:ident) : $extraty:ty $(= $default:expr)* ;)*
        build($call:expr);
        }*/
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

macro_rules! custom_keyword_impl {
  ($name:ident, $keyident:expr, $keydisp:expr) => {

    impl CustomKeyword for $name {
      fn ident() -> &'static str { $keyident }
      fn display() -> &'static str { $keydisp }
    }
  }}

macro_rules! custom_keyword {
  ($name:ident, $keyident:expr, $keydisp:expr) => {

    #[derive(Debug)]
    struct $name;

    custom_keyword_impl!($name, $keyident, $keydisp);

  }}



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



custom_keyword_impl!(DeclStorageConfig, "config", "build as keyword");
custom_keyword!(ConfigKeyword, "config", "config as keyword");
custom_keyword!(BuildKeyword, "build", "build as keyword");
custom_keyword_impl!(DeclStorageBuild, "build", "storage build config");
custom_keyword_impl!(AddExtraGenesis, "add_extra_genesis", "storage extra genesis");
custom_keyword_impl!(DeclStorageGetter, "get", "storage getter");
custom_keyword!(MapKeyword, "map", "map as keyword");
//custom_keyword_impl!(DeclStorageDefault, "=", "optional decl storage default");


