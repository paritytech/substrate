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
//! `decl_storage` macro transformation
// end::description[]

use srml_support_procedural_tools::syn_ext as ext;

use proc_macro::TokenStream;

use syn::Ident;

use super::*;

pub fn decl_storage_impl(input: TokenStream) -> TokenStream {
  let def = parse_macro_input!(input as StorageDefinition);
  //  panic!("{:?}", &def);

  // old macro naming convention (s replaces $)
  let StorageDefinition {
    runtime_crate,
    visibility,
    ident: sstoretype,
    module_ident: smodulename,
    mod_param: strait,
    crate_ident: scratename,
    content: ext::Braces { content: st, ..},
    extra_genesis,
    ..
  } = def;
  let scrate = runtime_crate.map(|rc|rc.ident.content).map(|i|quote!(#i)).unwrap_or_else(||
    if std::env::var("CARGO_PKG_NAME").unwrap() == "srml-support" {
      quote!( crate )
    } else {
      // TODO switch to more relevant srml_support? or use a rust2018 notation already
      quote!( ::runtime_support )
  });
 
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

    let extra_genesis = decl_store_extra_genesis(
      &scrate,
      &straitinstance,
      &straittype,
      &storage_lines,
      &extra_genesis,
    );

    let expanded = quote!{
      __decl_storage_items!(#scratename #straittype #straitinstance #st);
      #visibility trait #sstoretype {
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

fn decl_store_extra_genesis(
  scrate: &proc_macro2::TokenStream,
  straitinstance: &Ident,
  straittype: &syn::TypeParamBound,
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  extra_genesis: &Option<AddExtraGenesis>,
  ) -> proc_macro2::TokenStream {

  let mut is_trait_needed = false;
//      if getter.is_some() && config.is_some() {
//    ||  build.is_some()

    let mut config_field = Vec::new();
    let mut config_field_default = Vec::new();
    let mut builders = Vec::new();
    for sline in storage_lines.inner.iter() {
      let DeclStorageLine {
        name,
        getter,
        config,
        build,
        storage_type,
        default_value,
        ..
      } = sline;

      let is_simple = if let DeclStorageType::Simple(..) = storage_type { true } else { false };

      let mut opt_build; 
      // TODO find a name for this condition
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
        is_trait_needed = true;
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

    let mut has_scall = false;
    let mut scall = quote!{ ( |_, _, _|{} ) };
    let mut genesis_extrafields = Vec::new();
    let mut genesis_extrafields_default = Vec::new();

    // extra genesis
    if let Some(eg) = extra_genesis {
      for ex_content in eg.content.content.lines.inner.iter() {
        match ex_content {
          AddExtraGenesisLineEnum::AddExtraGenesisLine(AddExtraGenesisLine {
            attrs,
            extra_field,
            extra_type,
            default_seq,
            ..
          }) => {
            // warning there is some false positive here
            // TODO replace with `has_parametric_type(straitinstance)`
            // at this time just one of those in project
            if ext::has_parametric_type(&extra_type, straitinstance) {
              is_trait_needed = true;
            }
            let extrafield = &extra_field.content;
            genesis_extrafields.push(quote!{
              #attrs pub #extrafield : #extra_type ,
            });
            let extra_default = default_seq.inner.get(0).map(|d|&d.expr).map(|e|quote!{ #e })
              .unwrap_or_else(|| quote!{ Default::default() });
            genesis_extrafields_default.push(quote!{
              #extrafield : #extra_default ,
            });
          },
          AddExtraGenesisLineEnum::AddExtraGenesisBuild(AddExtraGenesisBuild{expr, ..}) => {
            if has_scall { panic!( "Only one build expression allowed for extra genesis" ) }
            let content = &expr.content;
            scall = quote!( ( #content ) );
            has_scall = true;
          },
        }
      }
    }


    let is_extra_genesis_needed = has_scall || config_field.len() > 0 || genesis_extrafields.len() > 0 || builders.len() > 0;
    if is_extra_genesis_needed {
        //__decl_genesis_config_items!([#straittype #straitinstance] [] [] [] [#( #slines )* ] [#scall] #st);
      let (fparam, sparam, ph_field, ph_default) = if is_trait_needed {
        (
          quote!(<#straitinstance: #straittype>),
          quote!(<#straitinstance>),
          quote!{
			      #[serde(skip)]
			      pub _genesis_phantom_data: #scrate::storage::generator::PhantomData<#straitinstance>,
          },
          quote!{
				    _genesis_phantom_data: Default::default(),
          },
        )
      } else {
        (quote!(), quote!(), quote!(), quote!())
      };
      quote!{
      
        #[derive(Serialize, Deserialize)]
        #[cfg(feature = "std")]
        #[serde(rename_all = "camelCase")]
        #[serde(deny_unknown_fields)]
        pub struct GenesisConfig#fparam {
          #ph_field
          #( #config_field )*
          #( #genesis_extrafields )*
        }

        #[cfg(feature = "std")]
        impl#fparam Default for GenesisConfig#sparam {
          fn default() -> Self {
            GenesisConfig {
              #ph_default
              #( #config_field_default )*
              #( #genesis_extrafields_default )*
            }
          }
        }

        #[cfg(feature = "std")]
        impl#fparam #scrate::runtime_primitives::BuildStorage for GenesisConfig#sparam
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
    } else { 
      quote!{}
    }
}


