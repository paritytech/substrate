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
    let decl_storage_items = decl_storage_items(
      &scrate,
      &straitinstance,
      &straittype,
      &scratename,
      &storage_lines,
    );
    let decl_store_items = decl_store_items(
      &storage_lines,
    );
    let impl_store_items = impl_store_items(
      &straitinstance,
      &storage_lines,
    );
    let impl_store_fns = impl_store_fns(
      &scrate,
      &straitinstance,
      &storage_lines,
    );
    let store_functions_to_metadata = store_functions_to_metadata(
      &scrate,
      &storage_lines,
    );
    let expanded = quote!{
      //__decl_storage_items!(#scratename #straittype #straitinstance #st);
      #decl_storage_items
      #visibility trait #sstoretype {
        //__decl_store_items!(#st);
        #decl_store_items
      }
      impl<#straitinstance: #straittype> #sstoretype for #smodulename<#straitinstance> {
        //__impl_store_items!(#straitinstance #st);
        #impl_store_items
      }
      impl<#straitinstance: #straittype> #smodulename<#straitinstance> {
        //__impl_store_fns!(#straitinstance #st);
        #impl_store_fns
        pub fn store_metadata() -> #scrate::storage::generator::StorageMetadata {
          #scrate::storage::generator::StorageMetadata {
            prefix: #scrate::storage::generator::DecodeDifferent::Encode(stringify!(#scratename)),
            //functions: __store_functions_to_metadata!(; #st ),
            functions: #store_functions_to_metadata ,
          }
        }
	
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

// __decl_storage_items!(#scratename #straittype #straitinstance #st);
fn decl_storage_items(
  scrate: &proc_macro2::TokenStream,
  straitinstance: &Ident,
  straittype: &syn::TypeParamBound,
  scratename: &Ident,
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  ) -> proc_macro2::TokenStream {

  let mut impls = Vec::new();
  for sline in storage_lines.inner.iter() {
    let DeclStorageLine {
      name,
      getter,
      config,
      build,
      storage_type,
      default_value,
      visibility,
      ..
    } = sline;

    let (is_simple, extracted_opt, stk, gettype) = match storage_type {
      DeclStorageType::Simple(ref st) => (true, ext::extract_type_option(st), None, st),
      DeclStorageType::Map(ref map) => (false, ext::extract_type_option(&map.value), Some(&map.key), &map.value),
    };
    let is_option = extracted_opt.is_some();
    let fielddefault = default_value.inner.get(0).as_ref().map(|d|&d.expr).map(|d|quote!{ #d })
        .unwrap_or_else(|| quote!{ Default::default() });

    let sty = extracted_opt.unwrap_or(quote!(#gettype));

    let option_simple_1 = if !is_option {
      // raw type case
      quote!( unwrap_or_else )
    } else {
      // Option<> type case
      quote!( or_else )
    };
    let imple = if is_simple {
      let mutate_impl = if !is_option {
        quote!{
          <Self as #scrate::storage::generator::StorageValue<#sty>>::put(&val, storage)
        }
      } else {
        quote!{
          match val {
            Some(ref val) => <Self as #scrate::storage::generator::StorageValue<#sty>>::put(&val, storage),
            None => <Self as #scrate::storage::generator::StorageValue<#sty>>::kill(storage),
          }
        }
      };

      // generator for value
      quote!{

        #visibility struct #name<#straitinstance: #straittype>(#scrate::storage::generator::PhantomData<#straitinstance>);

        impl<#straitinstance: #straittype> #scrate::storage::generator::StorageValue<#sty> for #name<#straitinstance> {
          type Query = #gettype;

          /// Get the storage key.
          fn key() -> &'static [u8] {
            stringify!(#scratename #name).as_bytes()
          }

          /// Load the value from the provided storage instance.
          fn get<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
            storage.get(<#name<#straitinstance> as #scrate::storage::generator::StorageValue<#sty>>::key())
              .#option_simple_1(|| #fielddefault)
          }

          /// Take a value from storage, removing it afterwards.
          fn take<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
            storage.take(<#name<#straitinstance> as #scrate::storage::generator::StorageValue<#sty>>::key())
              .#option_simple_1(|| #fielddefault)
          }

          /// Mutate the value under a key.
          fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(f: F, storage: &S) -> R {
            let mut val = <Self as #scrate::storage::generator::StorageValue<#sty>>::get(storage);

            let ret = f(&mut val);
            #mutate_impl ;
            ret
          }
        }

      }
    } else {
      let kty = stk.expect("is not simple; qed");
      let mutate_impl = if !is_option {
        quote!{
          <Self as #scrate::storage::generator::StorageMap<#kty, #sty>>::insert(key, &val, storage)
        }
      } else {
        quote!{
          match val {
            Some(ref val) => <Self as #scrate::storage::generator::StorageMap<#kty, #sty>>::insert(key, &val, storage),
            None => <Self as #scrate::storage::generator::StorageMap<#kty, #sty>>::remove(key, storage),
          }
        }
      };
      // generator for map
      quote!{
        #visibility struct #name<#straitinstance: #straittype>(#scrate::storage::generator::PhantomData<#straitinstance>);

        impl<#straitinstance: #straittype> #scrate::storage::generator::StorageMap<#kty, #sty> for #name<#straitinstance> {
          type Query = #gettype;

          /// Get the prefix key in storage.
          fn prefix() -> &'static [u8] {
				    stringify!(#scratename #name).as_bytes()
          }

          /// Get the storage key used to fetch a value corresponding to a specific key.
          fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
				    let mut key = <#name<#straitinstance> as #scrate::storage::generator::StorageMap<#kty, #sty>>::prefix().to_vec();
            #scrate::codec::Encode::encode_to(x, &mut key);
            key
          }

          /// Load the value associated with the given key from the map.
          fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
            let key = <#name<#straitinstance> as #scrate::storage::generator::StorageMap<#kty, #sty>>::key_for(key);
            storage.get(&key[..]).#option_simple_1(|| #fielddefault)
          }

          /// Take the value, reading and removing it.
          fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
            let key = <#name<#straitinstance> as #scrate::storage::generator::StorageMap<#kty, #sty>>::key_for(key);
            storage.take(&key[..]).#option_simple_1(|| #fielddefault)
          }

          /// Mutate the value under a key
          fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
            let mut val = <Self as #scrate::storage::generator::StorageMap<#kty, #sty>>::take(key, storage);

            let ret = f(&mut val);
            #mutate_impl ;
    				ret
	    		}

        }

      }
    };
    impls.push(imple)
  }

  quote!(#( #impls )*)

}


//  __decl_store_items!(#st);
fn decl_store_items(
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  ) -> proc_macro2::TokenStream {
  let mut items = Vec::new();
  for sline in storage_lines.inner.iter() {
    let DeclStorageLine {
      name,
      ..
    } = sline;
    items.push(quote!{
      type #name;
    });
  }
 
  quote!(#( #items )*)
}

// __impl_store_items!(#straitinstance #st);
fn impl_store_items(
  straitinstance: &Ident,
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  ) -> proc_macro2::TokenStream {
  let mut items = Vec::new();
  for sline in storage_lines.inner.iter() {
    let DeclStorageLine {
      name,
      ..
    } = sline;
    items.push(quote!{
      type #name = #name<#straitinstance>;
    });
  }
 
  quote!(#( #items )*)
}

//  __impl_store_fns!(#straitinstance #st);
fn impl_store_fns(
  scrate: &proc_macro2::TokenStream,
  straitinstance: &Ident,
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  ) -> proc_macro2::TokenStream {
  let mut items = Vec::new();
  for sline in storage_lines.inner.iter() {
    let DeclStorageLine {
      name,
      getter,
      config,
      build,
      storage_type,
      default_value,
      visibility,
      ..
    } = sline;

    if let Some(getter) = getter {
      let get_fn = &getter.getfn.content;
      let (is_simple, extracted_opt, stk, gettype) = match storage_type {
        DeclStorageType::Simple(ref st) => (true, ext::extract_type_option(st), None, st),
        DeclStorageType::Map(ref map) => (false, ext::extract_type_option(&map.value), Some(&map.key), &map.value),
      };

      let sty = extracted_opt.unwrap_or(quote!(#gettype));
      let item = if is_simple {
        quote!{
          pub fn #get_fn() -> #gettype {
            <#name<#straitinstance> as #scrate::storage::generator::StorageValue<#sty>> :: get(&#scrate::storage::RuntimeStorage)
          }
        }
      } else {
        let kty = stk.expect("is not simple; qed");
        // map
        quote!{
          pub fn #get_fn<K: #scrate::storage::generator::Borrow<#kty>>(key: K) -> #gettype {
            <#name<#straitinstance> as #scrate::storage::generator::StorageMap<#kty, #sty>> :: get(key.borrow(), &#scrate::storage::RuntimeStorage)
          }

        }
      };
      items.push(item);
    }
  }
 
  quote!(#( #items )*)
}

//  __impl_store_metadata!(#straitinstance #st);
//	__store_functions_to_metadata!(; $( $rest )* ),
fn store_functions_to_metadata (
  scrate: &proc_macro2::TokenStream,
  storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
  ) -> proc_macro2::TokenStream {
  let mut items = Vec::new();
  for sline in storage_lines.inner.iter() {
    let DeclStorageLine {
      attrs,
      name,
      getter,
      config,
      build,
      storage_type,
      default_value,
      visibility,
      ..
    } = sline;

      let (is_simple, extracted_opt, stk, gettype) = match storage_type {
        DeclStorageType::Simple(ref st) => (true, ext::extract_type_option(st), None, st),
        DeclStorageType::Map(ref map) => (false, ext::extract_type_option(&map.value), Some(&map.key), &map.value),
      };

      let is_option = extracted_opt.is_some();
      let sty = extracted_opt.unwrap_or(quote!(#gettype));
      let stype = if is_simple {
        let ssty = sty.to_string().replace(" ","");
        quote!{
          #scrate::storage::generator::StorageFunctionType::Plain(
            #scrate::storage::generator::DecodeDifferent::Encode(#ssty),
          )
        }
      } else {
        let kty = stk.expect("is not simple; qed");
        let kty = quote!(#kty).to_string().replace(" ","");
        let ssty = sty.to_string().replace(" ","");
        quote!{
          #scrate::storage::generator::StorageFunctionType::Map {
            key: #scrate::storage::generator::DecodeDifferent::Encode(#kty),
            value: #scrate::storage::generator::DecodeDifferent::Encode(#ssty),
          }
        }
      };
      let modifier = if !is_option {
        quote!{
				  #scrate::storage::generator::StorageFunctionModifier::Default
        }
      } else {
        quote!{
				  #scrate::storage::generator::StorageFunctionModifier::Optional
        }
      };
      let mut docs = Vec::new();
      for attr in attrs.inner.iter() {
        if let Some(syn::Meta::NameValue(syn::MetaNameValue{
          ref ident,
          ref lit,
          ..
        })) = attr.interpret_meta() {
          if ident == "doc" {
            docs.push(quote!(#lit));
          }
        }
      }
      let str_name = quote!(#name).to_string().replace(" ","");
      let item = quote! {
          #scrate::storage::generator::StorageFunctionMetadata {
            name: #scrate::storage::generator::DecodeDifferent::Encode(#str_name),
            modifier: #modifier,
            ty: #stype,
            documentation: #scrate::storage::generator::DecodeDifferent::Encode(&[ #( #docs ),* ]),
          }
      };
      items.push(item);
  }
 

  quote!{
   	#scrate::storage::generator::DecodeDifferent::Encode(&[
      #( #items ),*
		])
  }
}
