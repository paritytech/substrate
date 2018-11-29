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

use syn::{
	Ident,
	GenericParam,
};

use super::*;

pub fn decl_storage_impl(input: TokenStream) -> TokenStream {
	let def = parse_macro_input!(input as StorageDefinition);

	// old macro naming convention (s replaces $)
	let StorageDefinition {
		runtime_crate,
		visibility,
		ident: storetype,
		module_ident,
		mod_param: strait,
		crate_ident: cratename,
		content: ext::Braces { content: storage_lines, ..},
		extra_genesis,
		..
	} = def;
	let scrate = runtime_crate.map(|rc|rc.ident.content).map(|i|quote!(#i)).unwrap_or_else(||
		if ::std::env::var("CARGO_PKG_NAME").unwrap() == "srml-support" {
			quote!( crate )
		} else {
			// TODO switch to a more relevant srml_support? or use a rust2018 notation already
			quote!( ::runtime_support )
	});

	let (
		traitinstance,
		traittypes,
	) = if let GenericParam::Type(syn::TypeParam {ident, bounds, ..}) = strait {
		(ident, bounds)
	} else { panic!("Missing declare store generic params") };

	let traittype = traittypes.first().expect("a trait bound expected").into_value();

	let extra_genesis = decl_store_extra_genesis(
		&scrate,
		&traitinstance,
		&traittype,
		&storage_lines,
		&extra_genesis,
	);
	let decl_storage_items = decl_storage_items(
		&scrate,
		&traitinstance,
		&traittype,
		&cratename,
		&storage_lines,
	);
	let decl_store_items = decl_store_items(
		&storage_lines,
	);
	let impl_store_items = impl_store_items(
		&traitinstance,
		&storage_lines,
	);
	let impl_store_fns = impl_store_fns(
		&scrate,
		&traitinstance,
		&storage_lines,
	);
	let store_functions_to_metadata = store_functions_to_metadata(
		&scrate,
		&storage_lines,
	);
	let expanded = quote! {
		#decl_storage_items
		#visibility trait #storetype {
		#decl_store_items
		}
		impl<#traitinstance: #traittype> #storetype for #module_ident<#traitinstance> {
			#impl_store_items
		}
		impl<#traitinstance: #traittype> #module_ident<#traitinstance> {
			#impl_store_fns
			pub fn store_metadata() -> #scrate::storage::generator::StorageMetadata {
				#scrate::storage::generator::StorageMetadata {
					prefix: #scrate::storage::generator::DecodeDifferent::Encode(stringify!(#cratename)),
					functions: #store_functions_to_metadata ,
				}
			}
		}

		#extra_genesis

	};

	expanded.into()
}

fn decl_store_extra_genesis(
	scrate: &proc_macro2::TokenStream,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
	extra_genesis: &Option<AddExtraGenesis>,
) -> proc_macro2::TokenStream {

	let mut is_trait_needed = false;
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
		// TODO name this condition
		if getter.is_some() && config.is_some() {

			let ident = if let Some(ident) = config.as_ref().expect("previous condition; qed").expr.content.as_ref() {
			quote!( #ident )
		} else {
			let ident = &getter.as_ref().expect("previous condition; qed").getfn.content;
			quote!( #ident )
		};
		let option_extracteed = if let DeclStorageType::Simple(ref st) = storage_type {
			ext::extract_type_option(st)
		} else { None };
		let is_option = option_extracteed.is_some();
		let storage_type = option_extracteed.unwrap_or_else(||quote!( #storage_type ));
		config_field.push(quote!( pub #ident: #storage_type, ));
		opt_build = Some(build.as_ref().map(|b|&b.expr.content).map(|b|quote!( #b ))
			.unwrap_or_else(||quote!( (|config: &GenesisConfig<#traitinstance>| config.#ident.clone()) )));
		let fielddefault = default_value.inner.get(0).as_ref().map(|d|&d.expr).map(|d|
			if is_option {
				quote!( #d.unwrap_or_default() )
			} else {
				quote!( #d )
			}).unwrap_or_else(|| quote!( Default::default() ));
				config_field_default.push(quote!( #ident: #fielddefault, ));

			} else {
				opt_build = build.as_ref().map(|b|&b.expr.content).map(|b|quote!( #b ));
			}

			if let Some(builder) = opt_build {
				is_trait_needed = true;
				if is_simple {
					builders.push(quote!{{
						use #scrate::codec::Encode;
						let v = (#builder)(&self);
						r.insert(Self::hash(<#name<#traitinstance>>::key()).to_vec(), v.encode());
					}});
				} else {
					builders.push(quote!{{
						use #scrate::codec::Encode;
						let data = (#builder)(&self);
						for (k, v) in data.into_iter() {
							r.insert(Self::hash(&<#name<#traitinstance>>::key_for(k)).to_vec(), v.encode());
						}
					}});
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
						default_value,
						..
					}) => {
						if ext::has_parametric_type(&extra_type, traitinstance) {
							is_trait_needed = true;
						}
						let extrafield = &extra_field.content;
						genesis_extrafields.push(quote!{
							#attrs pub #extrafield: #extra_type,
						});
						let extra_default = default_value.inner.get(0).map(|d|&d.expr).map(|e|quote!{ #e })
							.unwrap_or_else(|| quote!( Default::default() ));
						genesis_extrafields_default.push(quote!{
							#extrafield: #extra_default,
						});
					},
					AddExtraGenesisLineEnum::AddExtraGenesisBuild(DeclStorageBuild{ expr, .. }) => {
						if has_scall { panic!( "Only one build expression allowed for extra genesis" ) }
						let content = &expr.content;
						scall = quote!( ( #content ) );
						has_scall = true;
					},
				}
			}
		}

		let is_extra_genesis_needed = has_scall
			|| config_field.len() > 0
			|| genesis_extrafields.len() > 0
			|| builders.len() > 0;
		if is_extra_genesis_needed {
			let (fparam, sparam, ph_field, ph_default) = if is_trait_needed {
				(
					quote!(<#traitinstance: #traittype>),
					quote!(<#traitinstance>),
					quote!{
						#[serde(skip)]
						pub _genesis_phantom_data: #scrate::storage::generator::PhantomData<#traitinstance>,
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
				impl#fparam #scrate::runtime_primitives::BuildStorage for GenesisConfig#sparam {

					fn build_storage(self) -> ::std::result::Result<(#scrate::runtime_primitives::StorageMap, #scrate::runtime_primitives::ChildrenStorageMap), String> {
						let mut r: #scrate::runtime_primitives::StorageMap = Default::default();
						let mut c: #scrate::runtime_primitives::ChildrenStorageMap = Default::default();

						#( #builders )*

						#scall(&mut r, &mut c, &self);

						Ok((r, c))
					}
				}
			}
		} else {
			quote!()
		}
}

fn decl_storage_items(
	scrate: &proc_macro2::TokenStream,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	cratename: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> proc_macro2::TokenStream {

	let mut impls = Vec::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			name,
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
		let fielddefault = default_value.inner.get(0).as_ref().map(|d|&d.expr).map(|d|quote!( #d ))
			.unwrap_or_else(|| quote!{ Default::default() });

		let typ = extracted_opt.unwrap_or(quote!( #gettype ));

		let option_simple_1 = if !is_option {
			// raw type case
			quote!( unwrap_or_else )
		} else {
			// Option<> type case
			quote!( or_else )
		};
		let implementation = if is_simple {
			let mutate_impl = if !is_option {
				quote!{
					<Self as #scrate::storage::generator::StorageValue<#typ>>::put(&val, storage)
				}
			} else {
				quote!{
					match val {
						Some(ref val) => <Self as #scrate::storage::generator::StorageValue<#typ>>::put(&val, storage),
						None => <Self as #scrate::storage::generator::StorageValue<#typ>>::kill(storage),
					}
				}
			};

			// generator for value
			quote!{

				#visibility struct #name<#traitinstance: #traittype>(#scrate::storage::generator::PhantomData<#traitinstance>);

				impl<#traitinstance: #traittype> #scrate::storage::generator::StorageValue<#typ> for #name<#traitinstance> {
					type Query = #gettype;

					/// Get the storage key.
					fn key() -> &'static [u8] {
						stringify!(#cratename #name).as_bytes()
					}

					/// Load the value from the provided storage instance.
					fn get<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
						storage.get(<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>>::key())
							.#option_simple_1(|| #fielddefault)
					}

					/// Take a value from storage, removing it afterwards.
					fn take<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
						storage.take(<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>>::key())
							.#option_simple_1(|| #fielddefault)
					}

					/// Mutate the value under a key.
					fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(f: F, storage: &S) -> R {
						let mut val = <Self as #scrate::storage::generator::StorageValue<#typ>>::get(storage);

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
					<Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::insert(key, &val, storage)
				}
			} else {
				quote!{
					match val {
						Some(ref val) => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::insert(key, &val, storage),
						None => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::remove(key, storage),
					}
				}
			};
			// generator for map
			quote!{
				#visibility struct #name<#traitinstance: #traittype>(#scrate::storage::generator::PhantomData<#traitinstance>);

				impl<#traitinstance: #traittype> #scrate::storage::generator::StorageMap<#kty, #typ> for #name<#traitinstance> {
					type Query = #gettype;

					/// Get the prefix key in storage.
					fn prefix() -> &'static [u8] {
						stringify!(#cratename #name).as_bytes()
					}

					/// Get the storage key used to fetch a value corresponding to a specific key.
					fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
						let mut key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::prefix().to_vec();
						#scrate::codec::Encode::encode_to(x, &mut key);
						key
					}

					/// Load the value associated with the given key from the map.
					fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
						let key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
						storage.get(&key[..]).#option_simple_1(|| #fielddefault)
					}

					/// Take the value, reading and removing it.
					fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
						let key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
						storage.take(&key[..]).#option_simple_1(|| #fielddefault)
					}

					/// Mutate the value under a key
					fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
						let mut val = <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::take(key, storage);

						let ret = f(&mut val);
						#mutate_impl ;
						ret
					}

				}

			}
		};
		impls.push(implementation)
	}

	quote!( #( #impls )* )

}


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

	quote!( #( #items )* )
}

fn impl_store_items(
	traitinstance: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> proc_macro2::TokenStream {
	let mut items = Vec::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			name,
			..
		} = sline;
		items.push(quote!{
			type #name = #name<#traitinstance>;
		});
	}

	quote!( #( #items )* )
}

fn impl_store_fns(
	scrate: &proc_macro2::TokenStream,
	traitinstance: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> proc_macro2::TokenStream {
	let mut items = Vec::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			name,
			getter,
			storage_type,
			..
		} = sline;

		if let Some(getter) = getter {
			let get_fn = &getter.getfn.content;
			let (is_simple, extracted_opt, stk, gettype) = match storage_type {
				DeclStorageType::Simple(ref st) => (true, ext::extract_type_option(st), None, st),
				DeclStorageType::Map(ref map) => (false, ext::extract_type_option(&map.value), Some(&map.key), &map.value),
			};

			let typ = extracted_opt.unwrap_or(quote!(#gettype));
			let item = if is_simple {
				quote!{
					pub fn #get_fn() -> #gettype {
						<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>> :: get(&#scrate::storage::RuntimeStorage)
					}
				}
			} else {
				let kty = stk.expect("is not simple; qed");
				// map
				quote!{
					pub fn #get_fn<K: #scrate::storage::generator::Borrow<#kty>>(key: K) -> #gettype {
						<#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>> :: get(key.borrow(), &#scrate::storage::RuntimeStorage)
					}
				}
			};
			items.push(item);
		}
	}

	quote!( #( #items )* )
}

fn store_functions_to_metadata (
	scrate: &proc_macro2::TokenStream,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> proc_macro2::TokenStream {

	let mut items = Vec::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			attrs,
			name,
			storage_type,
			..
		} = sline;

		let (is_simple, extracted_opt, stk, gettype) = match storage_type {
			DeclStorageType::Simple(ref st) => (true, ext::extract_type_option(st), None, st),
			DeclStorageType::Map(ref map) => (false, ext::extract_type_option(&map.value), Some(&map.key), &map.value),
		};

		let is_option = extracted_opt.is_some();
		let typ = extracted_opt.unwrap_or(quote!( #gettype ));
		let stype = if is_simple {
			let styp = typ.to_string().replace(" ","");
			quote!{
				#scrate::storage::generator::StorageFunctionType::Plain(
					#scrate::storage::generator::DecodeDifferent::Encode(#styp),
				)
			}
		} else {
			let kty = stk.expect("is not simple; qed");
			let kty = quote!(#kty).to_string().replace(" ","");
			let styp = typ.to_string().replace(" ","");
			quote!{
				#scrate::storage::generator::StorageFunctionType::Map {
					key: #scrate::storage::generator::DecodeDifferent::Encode(#kty),
					value: #scrate::storage::generator::DecodeDifferent::Encode(#styp),
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
