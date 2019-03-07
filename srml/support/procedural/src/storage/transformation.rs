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
use srml_support_procedural_tools::{generate_crate_access, generate_hidden_includes, clean_type_string};

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

use syn::{
	Ident,
	GenericParam,
	spanned::Spanned,
	parse::{
		Error,
		Result,
	},
	parse_macro_input,
};
use quote::quote;

use super::*;

// try macro but returning tokenized error
macro_rules! try_tok(( $expre : expr ) => {
	match $expre {
		Ok(r) => r,
		Err (err) => {
			return err.to_compile_error().into()
		}
	}
});

pub fn decl_storage_impl(input: TokenStream) -> TokenStream {
	let def = parse_macro_input!(input as StorageDefinition);

	let StorageDefinition {
		hidden_crate,
		visibility,
		ident: storetype,
		module_ident,
		mod_param: strait,
		crate_ident: cratename,
		content: ext::Braces { content: storage_lines, ..},
		extra_genesis,
		..
	} = def;
	let hidden_crate_name = hidden_crate.map(|rc| rc.ident.content).map(|i| i.to_string())
		.unwrap_or_else(|| "decl_storage".to_string());
	let scrate = generate_crate_access(&hidden_crate_name, "srml-support");
	let scrate_decl = generate_hidden_includes(
		&hidden_crate_name,
		"srml-support",
	);

	let (
		traitinstance,
		traittypes,
	) = if let GenericParam::Type(syn::TypeParam {ident, bounds, ..}) = strait {
		(ident, bounds)
	} else {
		return try_tok!(Err(Error::new(strait.span(), "Missing declare store generic params")));
	};

	let traittype =	if let Some(traittype) = traittypes.first() {
		traittype.into_value()
	} else {
		return try_tok!(Err(Error::new(traittypes.span(), "Trait bound expected")));
	};

	let extra_genesis = try_tok!(decl_store_extra_genesis(
		&scrate,
		&traitinstance,
		&traittype,
		&storage_lines,
		&extra_genesis,
	));
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
	let (store_default_struct, store_functions_to_metadata) = store_functions_to_metadata(
		&scrate,
		&traitinstance,
		&traittype,
		&storage_lines,
	);
	let cratename_string = cratename.to_string();
	let expanded = quote! {
		#scrate_decl
		#decl_storage_items
		#visibility trait #storetype {
			#decl_store_items
		}
		#store_default_struct
		impl<#traitinstance: #traittype> #storetype for #module_ident<#traitinstance> {
			#impl_store_items
		}
		impl<#traitinstance: 'static + #traittype> #module_ident<#traitinstance> {
			#impl_store_fns
			pub fn store_metadata() -> #scrate::storage::generator::StorageMetadata {
				#scrate::storage::generator::StorageMetadata {
					functions: #scrate::storage::generator::DecodeDifferent::Encode(#store_functions_to_metadata) ,
				}
			}
			pub fn store_metadata_functions() -> &'static [#scrate::storage::generator::StorageFunctionMetadata] {
				#store_functions_to_metadata
			}
			pub fn store_metadata_name() -> &'static str {
				#cratename_string
			}

		}

		#extra_genesis

	};

	expanded.into()
}

fn decl_store_extra_genesis(
	scrate: &TokenStream2,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
	extra_genesis: &Option<AddExtraGenesis>,
) -> Result<TokenStream2> {

	let mut is_trait_needed = false;
	let mut has_trait_field = false;
	let mut serde_complete_bound = std::collections::HashSet::new();
	let mut config_field = TokenStream2::new();
	let mut config_field_default = TokenStream2::new();
	let mut builders = TokenStream2::new();
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

		let type_infos = get_type_infos(storage_type);

		let mut opt_build;
		// need build line
		if let Some(ref config) = config {
			let ident = if let Some(ident) = config.expr.content.as_ref() {
				quote!( #ident )
			} else if let Some(ref getter) = getter {
				let ident = &getter.getfn.content;
				quote!( #ident )
			} else {
				return Err(syn::Error::new_spanned(name, format!("Invalid storage definiton, couldn't find config identifier: storage must either have a get identifier `get(ident)` or a defined config identifier `config(ident)`")));
			};
			if type_infos.kind.is_simple() && ext::has_parametric_type(type_infos.value_type, traitinstance) {
				is_trait_needed = true;
				has_trait_field = true;
			}

			serde_complete_bound.insert(type_infos.value_type);
			if let DeclStorageTypeInfosKind::Map { key_type, .. } = type_infos.kind {
				serde_complete_bound.insert(key_type);
			}
			let storage_type = type_infos.typ.clone();
			config_field.extend(match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!( pub #ident: #storage_type, )
				},
				DeclStorageTypeInfosKind::Map {key_type, .. } => {
					quote!( pub #ident: Vec<(#key_type, #storage_type)>, )
				},
			});
			opt_build = Some(build.as_ref().map(|b| &b.expr.content).map(|b|quote!( #b ))
				.unwrap_or_else(|| quote!( (|config: &GenesisConfig<#traitinstance>| config.#ident.clone()) )));

			let fielddefault = default_value.inner.as_ref().map(|d| &d.expr).map(|d|
				if type_infos.is_option {
					quote!( #d.unwrap_or_default() )
				} else {
					quote!( #d )
				}).unwrap_or_else(|| quote!( Default::default() ));

			config_field_default.extend(quote!( #ident: #fielddefault, ));
		} else {
			opt_build = build.as_ref().map(|b| &b.expr.content).map(|b| quote!( #b ));
		}

		let typ = type_infos.typ;
		if let Some(builder) = opt_build {
			is_trait_needed = true;
			builders.extend(match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!{{
						use #scrate::rstd::{cell::RefCell, marker::PhantomData};
						use #scrate::codec::{Encode, Decode};

						let storage = (RefCell::new(&mut r), PhantomData::<Self>::default());
						let v = (#builder)(&self);
						<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>>::put(&v, &storage);
					}}
				},
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					quote!{{
						use #scrate::rstd::{cell::RefCell, marker::PhantomData};
						use #scrate::codec::{Encode, Decode};

						let storage = (RefCell::new(&mut r), PhantomData::<Self>::default());
						let data = (#builder)(&self);
						for (k, v) in data.into_iter() {
							<#name<#traitinstance> as #scrate::storage::generator::StorageMap<#key_type, #typ>>::insert(&k, &v, &storage);
						}
					}}
				},
			});
		}

	}

	let mut has_scall = false;
	let mut scall = quote!{ ( |_, _, _| {} ) };
	let mut genesis_extrafields = TokenStream2::new();
	let mut genesis_extrafields_default = TokenStream2::new();

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
						has_trait_field = true;
					}

					serde_complete_bound.insert(extra_type);

					let extrafield = &extra_field.content;
					genesis_extrafields.extend(quote!{
						#attrs pub #extrafield: #extra_type,
					});
					let extra_default = default_value.inner.as_ref().map(|d| &d.expr).map(|e| quote!{ #e })
						.unwrap_or_else(|| quote!( Default::default() ));
					genesis_extrafields_default.extend(quote!{
						#extrafield: #extra_default,
					});
				},
				AddExtraGenesisLineEnum::AddExtraGenesisBuild(DeclStorageBuild{ expr, .. }) => {
					if has_scall {
						return Err(Error::new(expr.span(), "Only one build expression allowed for extra genesis"));
					}
					let content = &expr.content;
					scall = quote!( ( #content ) );
					has_scall = true;
				},
			}
		}
	}


	let serde_bug_bound = if !serde_complete_bound.is_empty() {
		let mut b_ser = String::new();
		let mut b_dser = String::new();
		// panic!("{:#?}", serde_complete_bound);
		serde_complete_bound.into_iter().for_each(|bound| {
			let stype = quote!(#bound);
			b_ser.push_str(&format!("{} : {}::serde::Serialize, ", stype, scrate));
			b_dser.push_str(&format!("{} : {}::serde::de::DeserializeOwned, ", stype, scrate));
		});

		quote! {
			#[serde(bound(serialize = #b_ser))]
			#[serde(bound(deserialize = #b_dser))]
		}
	} else {
		quote!()
	};

	let is_extra_genesis_needed = has_scall
		|| !config_field.is_empty()
		|| !genesis_extrafields.is_empty()
		|| !builders.is_empty();
	Ok(if is_extra_genesis_needed {
		let (fparam, sparam, ph_field, ph_default) = if is_trait_needed {
			if has_trait_field {
				// no phantom data required
				(
					quote!(<#traitinstance: #traittype>),
					quote!(<#traitinstance>),
					quote!(),
					quote!(),
				)
			} else {
				// need phantom data
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
			}
		} else {
			// do not even need type parameter
			(quote!(), quote!(), quote!(), quote!())
		};
		quote!{

			#[derive(#scrate::Serialize, #scrate::Deserialize)]
			#[cfg(feature = "std")]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			#serde_bug_bound
			pub struct GenesisConfig#fparam {
				#ph_field
				#config_field
				#genesis_extrafields
			}

			#[cfg(feature = "std")]
			impl#fparam Default for GenesisConfig#sparam {
				fn default() -> Self {
					GenesisConfig {
						#ph_default
						#config_field_default
						#genesis_extrafields_default
					}
				}
			}

			#[cfg(feature = "std")]
			impl#fparam #scrate::runtime_primitives::BuildStorage for GenesisConfig#sparam {

				fn build_storage(self) -> ::std::result::Result<(#scrate::runtime_primitives::StorageOverlay, #scrate::runtime_primitives::ChildrenStorageOverlay), String> {
					let mut r: #scrate::runtime_primitives::StorageOverlay = Default::default();
					let mut c: #scrate::runtime_primitives::ChildrenStorageOverlay = Default::default();

					#builders

					#scall(&mut r, &mut c, &self);

					Ok((r, c))
				}
			}
		}
	} else {
		quote!()
	})
}

fn decl_storage_items(
	scrate: &TokenStream2,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	cratename: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {

	let mut impls = TokenStream2::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			name,
			storage_type,
			default_value,
			visibility,
			..
		} = sline;

		let type_infos = get_type_infos(storage_type);
		let kind = type_infos.kind.clone();
		let i = impls::Impls {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault: default_value.inner.as_ref().map(|d| &d.expr).map(|d| quote!( #d ))
				.unwrap_or_else(|| quote!{ Default::default() }),
			prefix: format!("{} {}", cratename, name),
			name,
		};

		let implementation = match kind {
			DeclStorageTypeInfosKind::Simple => {
				i.simple_value()
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked: false } => {
				i.map(key_type)
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked: true } => {
				i.linked_map(key_type)
			},
		};
		impls.extend(implementation)
	}
	impls
}


fn decl_store_items(
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {
	storage_lines.inner.iter().map(|sline| &sline.name)
		.fold(TokenStream2::new(), |mut items, name| {
		items.extend(quote!(type #name;));
		items
	})
}

fn impl_store_items(
	traitinstance: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {
	storage_lines.inner.iter().map(|sline| &sline.name)
		.fold(TokenStream2::new(), |mut items, name| {
		items.extend(quote!(type #name = #name<#traitinstance>;));
		items
	})
}

fn impl_store_fns(
	scrate: &TokenStream2,
	traitinstance: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {
	let mut items = TokenStream2::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			name,
			getter,
			storage_type,
			..
		} = sline;

		if let Some(getter) = getter {
			let get_fn = &getter.getfn.content;

			let type_infos = get_type_infos(storage_type);
			let value_type = type_infos.value_type;

			let typ = type_infos.typ;
			let item = match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!{
						pub fn #get_fn() -> #value_type {
							<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>> :: get(&#scrate::storage::RuntimeStorage)
						}
					}
				},
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					quote!{
						pub fn #get_fn<K: #scrate::storage::generator::Borrow<#key_type>>(key: K) -> #value_type {
							<#name<#traitinstance> as #scrate::storage::generator::StorageMap<#key_type, #typ>> :: get(key.borrow(), &#scrate::storage::RuntimeStorage)
						}
					}
				}
			};
			items.extend(item);
		}
	}
	items
}

fn store_functions_to_metadata (
	scrate: &TokenStream2,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> (TokenStream2, TokenStream2) {

	let mut items = TokenStream2::new();
	let mut default_getter_struct_def = TokenStream2::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			attrs,
			name,
			storage_type,
			default_value,
			..
		} = sline;

		let type_infos = get_type_infos(storage_type);
		let value_type = type_infos.value_type;

		let typ = type_infos.typ;
		let styp = clean_type_string(&typ.to_string());
		let stype = match type_infos.kind {
			DeclStorageTypeInfosKind::Simple => {
				quote!{
					#scrate::storage::generator::StorageFunctionType::Plain(
						#scrate::storage::generator::DecodeDifferent::Encode(#styp),
					)
				}
			},
			DeclStorageTypeInfosKind::Map { key_type, .. } => {
				let kty = clean_type_string(&quote!(#key_type).to_string());
				quote!{
					#scrate::storage::generator::StorageFunctionType::Map {
						key: #scrate::storage::generator::DecodeDifferent::Encode(#kty),
						value: #scrate::storage::generator::DecodeDifferent::Encode(#styp),
					}
				}
			},
		};
		let modifier = if type_infos.is_option {
			quote!{
				#scrate::storage::generator::StorageFunctionModifier::Optional
			}
		} else {
			quote!{
				#scrate::storage::generator::StorageFunctionModifier::Default
			}
		};
		let default = default_value.inner.as_ref().map(|d| &d.expr)
			.map(|d| {
				quote!( #d )
			})
			.unwrap_or_else(|| quote!( Default::default() ));
		let mut docs = TokenStream2::new();
		for attr in attrs.inner.iter().filter_map(|v| v.interpret_meta()) {
			if let syn::Meta::NameValue(syn::MetaNameValue{
				ref ident,
				ref lit,
				..
			}) = attr {
				if ident == "doc" {
					docs.extend(quote!(#lit,));
				}
			}
		}
		let str_name = name.to_string();
		let struct_name = proc_macro2::Ident::new(&("__GetByteStruct".to_string() + &str_name), name.span());
		let cache_name = proc_macro2::Ident::new(&("__CACHE_GET_BYTE_STRUCT_".to_string() + &str_name), name.span());
		let item = quote! {
			#scrate::storage::generator::StorageFunctionMetadata {
				name: #scrate::storage::generator::DecodeDifferent::Encode(#str_name),
				modifier: #modifier,
				ty: #stype,
				default: #scrate::storage::generator::DecodeDifferent::Encode(
					#scrate::storage::generator::DefaultByteGetter(
						&#struct_name::<#traitinstance>(#scrate::rstd::marker::PhantomData)
					)
				),
				documentation: #scrate::storage::generator::DecodeDifferent::Encode(&[ #docs ]),
			},
		};
		items.extend(item);
		let def_get = quote! {
			pub struct #struct_name<#traitinstance>(pub #scrate::rstd::marker::PhantomData<#traitinstance>);
			#[cfg(feature = "std")]
			#[allow(non_upper_case_globals)]
			static #cache_name: #scrate::once_cell::sync::OnceCell<#scrate::rstd::vec::Vec<u8>> = #scrate::once_cell::sync::OnceCell::INIT;
			#[cfg(feature = "std")]
			impl<#traitinstance: #traittype> #scrate::storage::generator::DefaultByte for #struct_name<#traitinstance> {
				fn default_byte(&self) -> #scrate::rstd::vec::Vec<u8> {
					use #scrate::codec::Encode;
					#cache_name.get_or_init(|| {
						let def_val: #value_type = #default;
						<#value_type as Encode>::encode(&def_val)
					}).clone()
				}
			}
			#[cfg(not(feature = "std"))]
			impl<#traitinstance: #traittype> #scrate::storage::generator::DefaultByte for #struct_name<#traitinstance> {
				fn default_byte(&self) -> #scrate::rstd::vec::Vec<u8> {
					use #scrate::codec::Encode;
					let def_val: #value_type = #default;
					<#value_type as Encode>::encode(&def_val)
				}
			}
		};
		default_getter_struct_def.extend(def_get);
	}
	(default_getter_struct_def, quote!{
		{
			&[
				#items
			]
		}
	})
}


#[derive(Debug, Clone)]
pub(crate) struct DeclStorageTypeInfos<'a> {
	pub is_option: bool,
	pub typ: TokenStream2,
	pub value_type: &'a syn::Type,
	kind: DeclStorageTypeInfosKind<'a>,
}

#[derive(Debug, Clone)]
enum DeclStorageTypeInfosKind<'a> {
	Simple,
	Map {
		key_type: &'a syn::Type,
		is_linked: bool,
	},
}

impl<'a> DeclStorageTypeInfosKind<'a> {
	fn is_simple(&self) -> bool {
		match *self {
			DeclStorageTypeInfosKind::Simple => true,
			_ => false,
		}
	}
}

fn get_type_infos(storage_type: &DeclStorageType) -> DeclStorageTypeInfos {
	let (value_type, kind) = match storage_type {
		DeclStorageType::Simple(ref st) => (st, DeclStorageTypeInfosKind::Simple),
		DeclStorageType::Map(ref map) => (&map.value, DeclStorageTypeInfosKind::Map {
			key_type: &map.key,
			is_linked: false,
		}),
		DeclStorageType::LinkedMap(ref map) => (&map.value, DeclStorageTypeInfosKind::Map {
			key_type: &map.key,
			is_linked: true,
		}),
	};

	let extracted_type = ext::extract_type_option(value_type);
	let is_option = extracted_type.is_some();
	let typ = extracted_type.unwrap_or(quote!( #value_type ));

	DeclStorageTypeInfos {
		is_option,
		typ,
		value_type,
		kind,
	}

}
