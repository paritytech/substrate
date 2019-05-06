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

const NUMBER_OF_INSTANCE: usize = 16;

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
		mod_instance,
		mod_instantiable,
		mod_default_instance,
		crate_ident: cratename,
		content: ext::Braces { content: storage_lines, ..},
		extra_genesis,
		extra_genesis_skip_phantom_data_field,
		..
	} = def;

	let instance_opts = match get_instance_opts(mod_instance, mod_instantiable, mod_default_instance) {
		Ok(opts) => opts,
		Err(err) => return err.to_compile_error().into(),
	};

	let hidden_crate_name = hidden_crate.inner.map(|rc| rc.ident.content).map(|i| i.to_string())
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
		&instance_opts,
		&storage_lines,
		&extra_genesis.inner,
		extra_genesis_skip_phantom_data_field.inner.is_some(),
	));
	let decl_storage_items = decl_storage_items(
		&scrate,
		&traitinstance,
		&traittype,
		&instance_opts,
		&cratename,
		&storage_lines,
	);
	let decl_store_items = decl_store_items(
		&storage_lines,
	);
	let impl_store_items = impl_store_items(
		&traitinstance,
		&instance_opts.instance,
		&storage_lines,
	);
	let impl_store_fns = impl_store_fns(
		&scrate,
		&traitinstance,
		&instance_opts.instance,
		&storage_lines,
	);
	let (store_default_struct, store_functions_to_metadata) = store_functions_to_metadata(
		&scrate,
		&traitinstance,
		&traittype,
		&instance_opts,
		&storage_lines,
	);

	let InstanceOpts {
		instance,
		bound_instantiable,
		..
	} = instance_opts;

	let cratename_string = cratename.to_string();
	let expanded = quote! {
		#scrate_decl
		#decl_storage_items
		#visibility trait #storetype {
			#decl_store_items
		}
		#store_default_struct
		impl<#traitinstance: #traittype, #instance #bound_instantiable> #storetype for #module_ident<#traitinstance, #instance> {
			#impl_store_items
		}
		impl<#traitinstance: 'static + #traittype, #instance #bound_instantiable> #module_ident<#traitinstance, #instance> {
			#impl_store_fns
			#[doc(hidden)]
			pub fn store_metadata() -> #scrate::metadata::StorageMetadata {
				#scrate::metadata::StorageMetadata {
					functions: #scrate::metadata::DecodeDifferent::Encode(#store_functions_to_metadata) ,
				}
			}
			#[doc(hidden)]
			pub fn store_metadata_functions() -> &'static [#scrate::metadata::StorageFunctionMetadata] {
				#store_functions_to_metadata
			}
			#[doc(hidden)]
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
	instance_opts: &InstanceOpts,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
	extra_genesis: &Option<AddExtraGenesis>,
	extra_genesis_skip_phantom_data_field: bool,
) -> Result<TokenStream2> {

	let InstanceOpts {
		comma_instance,
		equal_default_instance,
		bound_instantiable,
		instance,
		..
	} = instance_opts;

	let mut is_trait_needed = false;
	let mut has_trait_field = false;
	let mut serde_complete_bound = std::collections::HashSet::new();
	let mut config_field = TokenStream2::new();
	let mut config_field_default = TokenStream2::new();
	let mut builders = TokenStream2::new();
	for sline in storage_lines.inner.iter() {

		let DeclStorageLine {
			attrs,
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
		if let Some(ref config) = config.inner {
			let ident = if let Some(ident) = config.expr.content.as_ref() {
				quote!( #ident )
			} else if let Some(ref getter) = getter.inner {
				let ident = &getter.getfn.content;
				quote!( #ident )
			} else {
				return Err(
					Error::new_spanned(
						name,
						"Invalid storage definiton, couldn't find config identifier: storage must either have a get identifier \
						`get(ident)` or a defined config identifier `config(ident)`"
					)
				);
			};
			if type_infos.kind.is_simple() && ext::has_parametric_type(type_infos.value_type, traitinstance) {
				is_trait_needed = true;
				has_trait_field = true;
			}

			serde_complete_bound.insert(type_infos.value_type);
			if let DeclStorageTypeInfosKind::Map { key_type, .. } = type_infos.kind {
				serde_complete_bound.insert(key_type);
			}

			// Propagate doc attributes.
			let attrs = attrs.inner.iter().filter_map(|a| a.parse_meta().ok()).filter(|m| m.name() == "doc");

			let storage_type = type_infos.typ.clone();
			config_field.extend(match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!( #( #[ #attrs ] )* pub #ident: #storage_type, )
				},
				DeclStorageTypeInfosKind::Map {key_type, .. } => {
					quote!( #( #[ #attrs ] )* pub #ident: Vec<(#key_type, #storage_type)>, )
				},
				DeclStorageTypeInfosKind::DoubleMap {key1_type, key2_type, .. } => {
					quote!( #( #[ #attrs ] )* pub #ident: Vec<(#key1_type, #key2_type, #storage_type)>, )
				},
			});
			opt_build = Some(build.inner.as_ref().map(|b| &b.expr.content).map(|b|quote!( #b ))
				.unwrap_or_else(|| quote!( (|config: &GenesisConfig<#traitinstance, #instance>| config.#ident.clone()) )));

			let fielddefault = default_value.inner.as_ref().map(|d| &d.expr).map(|d|
				if type_infos.is_option {
					quote!( #d.unwrap_or_default() )
				} else {
					quote!( #d )
				}).unwrap_or_else(|| quote!( Default::default() ));

			config_field_default.extend(quote!( #ident: #fielddefault, ));
		} else {
			opt_build = build.inner.as_ref().map(|b| &b.expr.content).map(|b| quote!( #b ));
		}

		let typ = type_infos.typ;
		if let Some(builder) = opt_build {
			is_trait_needed = true;
			builders.extend(match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!{{
						use #scrate::rstd::{cell::RefCell, marker::PhantomData};
						use #scrate::codec::{Encode, Decode};

						let v = (#builder)(&self);
						<#name<#traitinstance, #instance> as #scrate::storage::hashed::generator::StorageValue<#typ>>::put(&v, &storage);
					}}
				},
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					quote!{{
						use #scrate::rstd::{cell::RefCell, marker::PhantomData};
						use #scrate::codec::{Encode, Decode};

						let data = (#builder)(&self);
						for (k, v) in data.into_iter() {
							<#name<#traitinstance, #instance> as #scrate::storage::hashed::generator::StorageMap<#key_type, #typ>>::insert(&k, &v, &storage);
						}
					}}
				},
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					quote!{{
						use #scrate::rstd::{cell::RefCell, marker::PhantomData};
						use #scrate::codec::{Encode, Decode};

						let data = (#builder)(&self);
						for (k1, k2, v) in data.into_iter() {
							<#name<#traitinstance, #instance> as #scrate::storage::unhashed::generator::StorageDoubleMap<#key1_type, #key2_type, #typ>>::insert(&k1, &k2, &v, &storage);
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
		let (fparam_struct, fparam_impl, sparam, ph_field, ph_default) = if is_trait_needed {
			if (has_trait_field && instance.is_none()) || extra_genesis_skip_phantom_data_field {
				// no phantom data required
				(
					quote!(<#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance>),
					quote!(<#traitinstance: #traittype, #instance #bound_instantiable>),
					quote!(<#traitinstance, #instance>),
					quote!(),
					quote!(),
				)
			} else {
				// need phantom data
				(
					quote!(<#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance>),
					quote!(<#traitinstance: #traittype, #instance #bound_instantiable>),
					quote!(<#traitinstance, #instance>),

					quote!{
						#[serde(skip)]
						pub _genesis_phantom_data: #scrate::rstd::marker::PhantomData<(#traitinstance #comma_instance)>,
					},
					quote!{
						_genesis_phantom_data: Default::default(),
					},
				)
			}
		} else {
			// do not even need type parameter
			(quote!(), quote!(), quote!(), quote!(), quote!())
		};
		quote!{

			#[derive(#scrate::Serialize, #scrate::Deserialize)]
			#[cfg(feature = "std")]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			#serde_bug_bound
			pub struct GenesisConfig#fparam_struct {
				#ph_field
				#config_field
				#genesis_extrafields
			}

			#[cfg(feature = "std")]
			impl#fparam_impl Default for GenesisConfig#sparam {
				fn default() -> Self {
					GenesisConfig {
						#ph_default
						#config_field_default
						#genesis_extrafields_default
					}
				}
			}

			#[cfg(feature = "std")]
			impl#fparam_impl #scrate::runtime_primitives::BuildStorage for GenesisConfig#sparam {
				fn assimilate_storage(self, r: &mut #scrate::runtime_primitives::StorageOverlay, c: &mut #scrate::runtime_primitives::ChildrenStorageOverlay) -> ::std::result::Result<(), String> {
					use #scrate::rstd::cell::RefCell;
					let storage = RefCell::new(r);

					#builders

					let r = storage.into_inner();

					#scall(r, c, &self);

					Ok(())
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
	instance_opts: &InstanceOpts,
	cratename: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {

	let mut impls = TokenStream2::new();

	let InstanceOpts {
		instance,
		default_instance,
		instantiable,
		..
	} = instance_opts;

	let build_prefix = |cratename, name| format!("{} {}", cratename, name);

	// Build Instantiable trait
	if instance.is_some() {
		let mut const_names = vec![];

		for sline in storage_lines.inner.iter() {
			let DeclStorageLine {
				storage_type,
				name,
				..
			} = sline;

			let prefix = build_prefix(cratename, name);

			let type_infos = get_type_infos(storage_type);

			let const_name = syn::Ident::new(&format!("{}{}", impls::PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site());
			let partial_const_value = prefix.clone();
			const_names.push((const_name, partial_const_value));

			if let DeclStorageTypeInfosKind::Map { is_linked: true, .. } = type_infos.kind {
				let const_name = syn::Ident::new(&format!("{}{}", impls::HEAD_KEY_FOR, name.to_string()), proc_macro2::Span::call_site());
				let partial_const_value = format!("head of {}", prefix);
				const_names.push((const_name, partial_const_value));
			}
		}

		// Declare Instance trait
		{
			let mut const_impls = TokenStream2::new();
			for (const_name, _) in &const_names {
				const_impls.extend(quote! {
					const #const_name: &'static str;
				});
			}

			impls.extend(quote! {
				/// Tag a type as an instance of a module.
				/// 
				/// Defines storage prefixes, they must be unique.
				pub trait #instantiable: 'static {
					#const_impls
				}
			});
		}

		let instances = (0..NUMBER_OF_INSTANCE)
			.map(|i| {
				let name = format!("Instance{}", i);
				let ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
				(name, ident, quote! {#[doc=r"Module instance"]})
			})
			.chain(default_instance.clone().map(|ident| (String::new(), ident, quote! {#[doc=r"Default module instance"]})));

		// Impl Instance trait for instances
		for (prefix, ident, doc) in instances {
			let mut const_impls = TokenStream2::new();

			for (const_name, partial_const_value) in &const_names {
				let const_value = format!("{}{}", partial_const_value, prefix);
				const_impls.extend(quote! {
					const #const_name: &'static str = #const_value;
				});
			}

			impls.extend(quote! {
				// Those trait are derived because of wrong bounds for generics
				#[cfg_attr(feature = "std", derive(Debug))]
				#[derive(Clone, Eq, PartialEq, #scrate::codec::Encode, #scrate::codec::Decode)]
				#doc
				pub struct #ident;
				impl #instantiable for #ident {
					#const_impls
				}
			});
		}
	}

	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			attrs,
			name,
			storage_type,
			default_value,
			visibility,
			..
		} = sline;

		let type_infos = get_type_infos(storage_type);
		let kind = type_infos.kind.clone();
		// Propagate doc attributes.
		let attrs = attrs.inner.iter().filter_map(|a| a.parse_meta().ok()).filter(|m| m.name() == "doc");

		let i = impls::Impls {
			scrate,
			visibility,
			cratename,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault: default_value.inner.as_ref().map(|d| &d.expr).map(|d| quote!( #d ))
				.unwrap_or_else(|| quote!{ Default::default() }),
			prefix: build_prefix(cratename, name),
			name,
			attrs,
		};

		let implementation = match kind {
			DeclStorageTypeInfosKind::Simple => {
				i.simple_value()
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked: false, hasher } => {
				i.map(hasher.into_storage_hasher_struct(), key_type)
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked: true, hasher } => {
				i.linked_map(hasher.into_storage_hasher_struct(), key_type)
			},
			DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, key2_hasher, hasher } => {
				i.double_map(hasher.into_storage_hasher_struct(), key1_type, key2_type, key2_hasher)
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
	instance: &Option<syn::Ident>,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {
	storage_lines.inner.iter().map(|sline| &sline.name)
		.fold(TokenStream2::new(), |mut items, name| {
			items.extend(
				quote!(
					type #name = #name<#traitinstance, #instance>;
				)
			);
			items
	})
}

fn impl_store_fns(
	scrate: &TokenStream2,
	traitinstance: &Ident,
	instance: &Option<syn::Ident>,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> TokenStream2 {
	let mut items = TokenStream2::new();
	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			attrs,
			name,
			getter,
			storage_type,
			..
		} = sline;

		if let Some(getter) = getter.inner.as_ref() {
			let get_fn = &getter.getfn.content;

			let type_infos = get_type_infos(storage_type);
			let value_type = type_infos.value_type;

			// Propagate doc attributes.
			let attrs = attrs.inner.iter().filter_map(|a| a.parse_meta().ok()).filter(|m| m.name() == "doc");

			let typ = type_infos.typ;
			let item = match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					quote!{
						#( #[ #attrs ] )*
						pub fn #get_fn() -> #value_type {
							<#name<#traitinstance, #instance> as #scrate::storage::hashed::generator::StorageValue<#typ>> :: get(&#scrate::storage::RuntimeStorage)
						}
					}
				},
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					quote!{
						#( #[ #attrs ] )*
						pub fn #get_fn<K: #scrate::rstd::borrow::Borrow<#key_type>>(key: K) -> #value_type {
							<#name<#traitinstance, #instance> as #scrate::storage::hashed::generator::StorageMap<#key_type, #typ>> :: get(key.borrow(), &#scrate::storage::RuntimeStorage)
						}
					}
				}
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					quote!{
						pub fn #get_fn<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> #value_type
						where
							KArg1: #scrate::rstd::borrow::Borrow<#key1_type>,
							KArg2: #scrate::rstd::borrow::Borrow<#key2_type>,
						{
							<#name<#traitinstance> as #scrate::storage::unhashed::generator::StorageDoubleMap<#key1_type, #key2_type, #typ>> :: get(k1.borrow(), k2.borrow(), &#scrate::storage::RuntimeStorage)
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
	instance_opts: &InstanceOpts,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
) -> (TokenStream2, TokenStream2) {

	let InstanceOpts {
		comma_instance,
		equal_default_instance,
		bound_instantiable,
		instance,
		..
	} = instance_opts;

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
					#scrate::metadata::StorageFunctionType::Plain(
						#scrate::metadata::DecodeDifferent::Encode(#styp),
					)
				}
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked, hasher } => {
				let hasher = hasher.into_metadata();
				let kty = clean_type_string(&quote!(#key_type).to_string());
				quote!{
					#scrate::metadata::StorageFunctionType::Map {
						hasher: #scrate::metadata::#hasher,
						key: #scrate::metadata::DecodeDifferent::Encode(#kty),
						value: #scrate::metadata::DecodeDifferent::Encode(#styp),
						is_linked: #is_linked,
					}
				}
			},
			DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, key2_hasher, hasher } => {
				let hasher = hasher.into_metadata();
				let k1ty = clean_type_string(&quote!(#key1_type).to_string());
				let k2ty = clean_type_string(&quote!(#key2_type).to_string());
				let k2_hasher = clean_type_string(&key2_hasher.to_string());
				quote!{
					#scrate::metadata::StorageFunctionType::DoubleMap {
						hasher: #scrate::metadata::#hasher,
						key1: #scrate::metadata::DecodeDifferent::Encode(#k1ty),
						key2: #scrate::metadata::DecodeDifferent::Encode(#k2ty),
						value: #scrate::metadata::DecodeDifferent::Encode(#styp),
						key2_hasher: #scrate::metadata::DecodeDifferent::Encode(#k2_hasher),
					}
				}
			},
		};
		let modifier = if type_infos.is_option {
			quote!{
				#scrate::metadata::StorageFunctionModifier::Optional
			}
		} else {
			quote!{
				#scrate::metadata::StorageFunctionModifier::Default
			}
		};
		let default = default_value.inner.as_ref().map(|d| &d.expr)
			.map(|d| {
				quote!( #d )
			})
			.unwrap_or_else(|| quote!( Default::default() ));
		let mut docs = TokenStream2::new();
		for attr in attrs.inner.iter().filter_map(|v| v.parse_meta().ok()) {
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
			#scrate::metadata::StorageFunctionMetadata {
				name: #scrate::metadata::DecodeDifferent::Encode(#str_name),
				modifier: #modifier,
				ty: #stype,
				default: #scrate::metadata::DecodeDifferent::Encode(
					#scrate::metadata::DefaultByteGetter(
						&#struct_name::<#traitinstance, #instance>(#scrate::rstd::marker::PhantomData)
					)
				),
				documentation: #scrate::metadata::DecodeDifferent::Encode(&[ #docs ]),
			},
		};
		items.extend(item);
		let def_get = quote! {
			#[doc(hidden)]
			pub struct #struct_name<#traitinstance, #instance #bound_instantiable #equal_default_instance>(pub #scrate::rstd::marker::PhantomData<(#traitinstance #comma_instance)>);
			#[cfg(feature = "std")]
			#[allow(non_upper_case_globals)]
			static #cache_name: #scrate::once_cell::sync::OnceCell<#scrate::rstd::vec::Vec<u8>> = #scrate::once_cell::sync::OnceCell::INIT;
			#[cfg(feature = "std")]
			impl<#traitinstance: #traittype, #instance #bound_instantiable> #scrate::metadata::DefaultByte for #struct_name<#traitinstance, #instance> {
				fn default_byte(&self) -> #scrate::rstd::vec::Vec<u8> {
					use #scrate::codec::Encode;
					#cache_name.get_or_init(|| {
						let def_val: #value_type = #default;
						<#value_type as Encode>::encode(&def_val)
					}).clone()
				}
			}
			#[cfg(not(feature = "std"))]
			impl<#traitinstance: #traittype, #instance #bound_instantiable> #scrate::metadata::DefaultByte for #struct_name<#traitinstance, #instance> {
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
		hasher: HasherKind,
		key_type: &'a syn::Type,
		is_linked: bool,
	},
	DoubleMap {
		hasher: HasherKind,
		key1_type: &'a syn::Type,
		key2_type: &'a syn::Type,
		key2_hasher: TokenStream2,
	}
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
			hasher: map.hasher.inner.as_ref().map(|h| h.into()).unwrap_or(HasherKind::Blake2_256),
			key_type: &map.key,
			is_linked: false,
		}),
		DeclStorageType::LinkedMap(ref map) => (&map.value, DeclStorageTypeInfosKind::Map {
			hasher: map.hasher.inner.as_ref().map(|h| h.into()).unwrap_or(HasherKind::Blake2_256),
			key_type: &map.key,
			is_linked: true,
		}),
		DeclStorageType::DoubleMap(ref map) => (&map.value, DeclStorageTypeInfosKind::DoubleMap {
			hasher: map.hasher.inner.as_ref().map(|h| h.into()).unwrap_or(HasherKind::Blake2_256),
			key1_type: &map.key1,
			key2_type: &map.key2.content,
			key2_hasher: { let h = &map.key2_hasher; quote! { #h } },
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

#[derive(Default)]
pub(crate) struct InstanceOpts {
	pub instance: Option<syn::Ident>,
	pub default_instance: Option<syn::Ident>,
	pub instantiable: Option<syn::Ident>,
	pub comma_instance: TokenStream2,
	pub equal_default_instance: TokenStream2,
	pub bound_instantiable: TokenStream2,
}

fn get_instance_opts(
	instance: Option<syn::Ident>,
	instantiable: Option<syn::Ident>,
	default_instance: Option<syn::Ident>,
) -> syn::Result<InstanceOpts> {

	let right_syntax = "Should be $Instance: $Instantiable = $DefaultInstance";

	match (instance, instantiable, default_instance) {
		(Some(instance), Some(instantiable), default_instance_def) => {
			let (equal_default_instance, default_instance) = if let Some(default_instance) = default_instance_def {
				(quote!{= #default_instance}, Some(default_instance))
			} else {
				(quote!{}, None)
			};
			Ok(InstanceOpts {
				comma_instance: quote!{, #instance},
				equal_default_instance,
				bound_instantiable: quote!{: #instantiable},
				instance: Some(instance),
				default_instance,
				instantiable: Some(instantiable),
			})
		},
		(None, None, None) => Ok(Default::default()),
		(Some(instance), None, _) => Err(syn::Error::new(instance.span(), format!("Expect instantiable trait bound for instance: {}. {}", instance, right_syntax))),
		(None, Some(instantiable), _) => Err(syn::Error::new(instantiable.span(), format!("Expect instance generic for bound instantiable: {}. {}", instantiable, right_syntax))),
		(None, _, Some(default_instance)) => Err(syn::Error::new(default_instance.span(), format!("Expect instance generic for default instance: {}. {}", default_instance, right_syntax))),
	}
}
