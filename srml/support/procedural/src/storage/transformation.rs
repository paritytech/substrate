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

//! `decl_storage` macro transformation

use srml_support_procedural_tools::syn_ext as ext;
use srml_support_procedural_tools::{
	generate_crate_access, generate_hidden_includes, clean_type_string
};

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Span};

use syn::{
	Ident,
	GenericParam,
	WhereClause,
	spanned::Spanned,
	parse::{
		Error,
		Result,
	},
	parse_macro_input,
};
use quote::{quote, quote_spanned};

use super::*;

const NUMBER_OF_INSTANCE: usize = 16;
const DEFAULT_INSTANTIABLE_TRAIT_NAME: &str = "__GeneratedInstantiable";
const DEFAULT_INSTANCE_NAME: &str = "__GeneratedInstance";
const INHERENT_INSTANCE_NAME: &str = "__InherentHiddenInstance";

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
		where_clause,
		..
	} = def;

	let instance_opts = match get_instance_opts(
		mod_instance,
		mod_instantiable,
		mod_default_instance
	) {
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
		&where_clause,
	));
	let decl_storage_items = decl_storage_items(
		&scrate,
		&traitinstance,
		&traittype,
		&instance_opts,
		&cratename,
		&storage_lines,
		&where_clause,
	).unwrap_or_else(|err| err.to_compile_error());

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
	let (store_default_struct, store_metadata) = store_functions_to_metadata(
		&scrate,
		&traitinstance,
		&traittype,
		&instance_opts,
		&storage_lines,
		&where_clause,
		&cratename,
	);

	let InstanceOpts {
		instance,
		bound_instantiable,
		..
	} = instance_opts;

	let expanded = quote! {
		use #scrate::{
			StorageValue as _,
			StorageMap as _,
			StorageLinkedMap as _,
			StorageDoubleMap as _
		};

		#scrate_decl
		#decl_storage_items
		#visibility trait #storetype {
			#decl_store_items
		}
		#store_default_struct
		impl<#traitinstance: #traittype, #instance #bound_instantiable> #storetype
			for #module_ident<#traitinstance, #instance> #where_clause
		{
			#impl_store_items
		}
		impl<#traitinstance: 'static + #traittype, #instance #bound_instantiable>
			#module_ident<#traitinstance, #instance> #where_clause
		{
			#impl_store_fns
			#[doc(hidden)]
			pub fn storage_metadata() -> #scrate::metadata::StorageMetadata {
				#store_metadata
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
	where_clause: &Option<syn::WhereClause>,
) -> Result<TokenStream2> {

	let InstanceOpts {
		equal_default_instance,
		bound_instantiable,
		instance,
		..
	} = instance_opts;

	let mut is_trait_needed = false;
	let mut serde_complete_bound = Vec::new();
	let mut config_field = TokenStream2::new();
	let mut config_field_default = TokenStream2::new();
	let mut builders = TokenStream2::new();
	let mut assimilate_require_generic = instance.is_some();
	let mut builders_clone_bound = Vec::new();

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

		let opt_build = build
			.inner
			.as_ref()
			.map(|b| {
				assimilate_require_generic |= ext::expr_contains_ident(&b.expr.content, traitinstance);
				&b.expr.content
			})
			.map(|b| quote!( #b ));

		// need build line
		let builder = if let Some(ref config) = config.inner {
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

			if ext::type_contains_ident(type_infos.value_type, traitinstance) {
				is_trait_needed = true;
			}

			if opt_build.is_none() {
				builders_clone_bound.push(type_infos.value_type.clone());
			}

			let value_type = &type_infos.value_type;
			serde_complete_bound.push(quote!( #value_type ));
			match type_infos.kind {
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					serde_complete_bound.push(quote!( #key_type ));
					is_trait_needed = is_trait_needed
						|| ext::type_contains_ident(key_type, traitinstance);

					if opt_build.is_none() {
						builders_clone_bound.push(key_type.clone());
					}
				},
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					serde_complete_bound.push(quote!( #key1_type ));
					serde_complete_bound.push(quote!( #key2_type ));
					is_trait_needed = is_trait_needed
						|| ext::type_contains_ident(key1_type, traitinstance)
						|| ext::type_contains_ident(key2_type, traitinstance);
					if opt_build.is_none() {
						builders_clone_bound.push(key1_type.clone());
						builders_clone_bound.push(key2_type.clone());
					}
				},
				_ => {},
			}

			if type_infos.is_option {
				serde_complete_bound.push(type_infos.typ.clone());
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

			let fielddefault = default_value.inner.as_ref().map(|d| &d.expr).map(|d|
				if type_infos.is_option {
					quote!( #d.unwrap_or_default() )
				} else {
					quote!( #d )
				}).unwrap_or_else(|| quote!( Default::default() ));

			config_field_default.extend(quote!( #ident: #fielddefault, ));

			opt_build.or_else(|| Some(quote!( (|config: &Self| config.#ident.clone()) )))
		} else {
			opt_build
		};

		let typ = type_infos.typ;
		if let Some(builder) = builder {
			builders.extend(match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance) {
						assimilate_require_generic = true;
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					quote!{{
						let v = (#builder)(&self);
						<
							#name<#struct_trait #instance> as
							#scrate::storage::StorageValue<#typ>
						>::put::<#typ>(v);
					}}
				},
				DeclStorageTypeInfosKind::Map { key_type, is_linked, .. } => {
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key_type, traitinstance)
					{
						assimilate_require_generic = true;
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					let map = if is_linked {
						quote! { StorageLinkedMap }
					} else {
						quote! { StorageMap }
					};

					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k, v)| {
							<
								#name<#struct_trait #instance> as
								#scrate::storage::#map<#key_type, #typ>
							>::insert::<#key_type, #typ>(k, v);
						});
					}}
				},
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key1_type, traitinstance)
						|| ext::type_contains_ident(key2_type, traitinstance)
					{
						assimilate_require_generic = true;
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k1, k2, v)| {
							<
								#name<#struct_trait #instance> as
								#scrate::storage::StorageDoubleMap<#key1_type, #key2_type, #typ>
							>::insert::<#key1_type, #key2_type, #typ>(k1, k2, v);
						});
					}}
				},
			});
		}
	}

	let mut has_scall = false;
	let mut scall = quote!{ let scall: fn(&Self) = |_| {}; scall };
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
					if ext::type_contains_ident(&extra_type, traitinstance) {
						is_trait_needed = true;
					}

					serde_complete_bound.push(quote!( #extra_type ));

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
					assimilate_require_generic |= ext::expr_contains_ident(&expr.content, traitinstance);
					let content = &expr.content;
					scall = quote_spanned! { expr.span() =>
						let scall: fn(&Self) = #content; scall
					};
					has_scall = true;
				},
			}
		}
	}

	let serde_bug_bound = if !serde_complete_bound.is_empty() {
		let mut b_ser = String::new();
		let mut b_dser = String::new();

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
	if is_extra_genesis_needed {
		let (inherent_instance, inherent_bound_instantiable) = if instance.is_some() {
			(instance.clone(), bound_instantiable.clone())
		} else {
			let instantiable = Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, Span::call_site());
			(
				Some(Ident::new(DEFAULT_INSTANCE_NAME, Span::call_site())),
				quote!(: #instantiable),
			)
		};

		let (fparam_struct, fparam_impl, sparam, build_storage_impl) = if is_trait_needed {
			(
				quote!(<#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance>),
				quote!(<#traitinstance: #traittype, #instance #bound_instantiable>),
				quote!(<#traitinstance, #instance>),
				quote!(<#traitinstance: #traittype, #inherent_instance #inherent_bound_instantiable>),
			)
		} else {
			// do not even need type parameter
			(
				quote!(),
				quote!(),
				quote!(),
				quote!(<#traitinstance: #traittype, #inherent_instance #inherent_bound_instantiable>),
			)
		};

		let (fn_generic, fn_traitinstance) = if !is_trait_needed && assimilate_require_generic {
			(
				quote!( <#traitinstance: #traittype, #instance #bound_instantiable> ),
				quote!( #traitinstance, #instance )
			)
		} else {
			(quote!(), quote!())
		};

		let impl_trait = quote!(BuildModuleGenesisStorage<#traitinstance, #inherent_instance>);

		let extend_where_clause = |to_extend: &mut WhereClause| {
			if let Some(where_clause) = where_clause {
				to_extend.predicates.extend(where_clause.predicates.iter().cloned());
			}
		};

		let mut genesis_where_clause: WhereClause = syn::parse_quote!(
			where #( #builders_clone_bound: Clone ),*
		);
		let mut fn_where_clause = genesis_where_clause.clone();


		let mut build_storage_where_clause = genesis_where_clause.clone();
		extend_where_clause(&mut build_storage_where_clause);

		if is_trait_needed {
			extend_where_clause(&mut genesis_where_clause);
		} else if assimilate_require_generic {
			extend_where_clause(&mut fn_where_clause);
		}

		let res = quote!{
			#[derive(#scrate::Serialize, #scrate::Deserialize)]
			#[cfg(feature = "std")]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			#serde_bug_bound
			pub struct GenesisConfig#fparam_struct #genesis_where_clause {
				#config_field
				#genesis_extrafields
			}

			#[cfg(feature = "std")]
			impl#fparam_impl Default for GenesisConfig#sparam #genesis_where_clause {
				fn default() -> Self {
					GenesisConfig {
						#config_field_default
						#genesis_extrafields_default
					}
				}
			}

			#[cfg(feature = "std")]
			impl#fparam_impl GenesisConfig#sparam #genesis_where_clause {
				pub fn build_storage #fn_generic (self) -> std::result::Result<
					(
						#scrate::sr_primitives::StorageOverlay,
						#scrate::sr_primitives::ChildrenStorageOverlay,
					),
					String
				> #fn_where_clause {
					let mut storage = (Default::default(), Default::default());
					self.assimilate_storage::<#fn_traitinstance>(&mut storage)?;
					Ok(storage)
				}

				/// Assimilate the storage for this module into pre-existing overlays.
				pub fn assimilate_storage #fn_generic (
					self,
					tuple_storage: &mut (
						#scrate::sr_primitives::StorageOverlay,
						#scrate::sr_primitives::ChildrenStorageOverlay,
					),
				) -> std::result::Result<(), String> #fn_where_clause {
					#scrate::with_storage(tuple_storage, || {
						#builders

						#scall(&self);

						Ok(())
					})
				}
			}

			#[cfg(feature = "std")]
			impl#build_storage_impl #scrate::sr_primitives::#impl_trait
				for GenesisConfig#sparam #build_storage_where_clause
			{
				fn build_module_genesis_storage(
					self,
					storage: &mut (
						#scrate::sr_primitives::StorageOverlay,
						#scrate::sr_primitives::ChildrenStorageOverlay,
					),
				) -> std::result::Result<(), String> {
					self.assimilate_storage::<#fn_traitinstance> (storage)
				}
			}
		};

		Ok(res)
	} else {
		Ok(quote!())
	}
}

fn create_and_impl_instance(
	instance_prefix: &str,
	ident: &Ident,
	doc: &TokenStream2,
	const_names: &[(Ident, String, String)],
	scrate: &TokenStream2,
	instantiable: &Ident,
	cratename: &Ident,
) -> TokenStream2 {
	let mut const_impls = TokenStream2::new();

	for (const_name, const_value_prefix, const_value_suffix) in const_names {
		let const_value = format!("{}{}{}", const_value_prefix, instance_prefix, const_value_suffix);
		const_impls.extend(quote! {
			const #const_name: &'static str = #const_value;
		});
	}

	let prefix = format!("{}{}", instance_prefix, cratename.to_string());

	quote! {
		// Those trait are derived because of wrong bounds for generics
		#[cfg_attr(feature = "std", derive(Debug))]
		#[derive(Clone, Eq, PartialEq, #scrate::codec::Encode, #scrate::codec::Decode)]
		#doc
		pub struct #ident;
		impl #instantiable for #ident {
			const PREFIX: &'static str = #prefix;
			#const_impls
		}
	}
}

fn decl_storage_items(
	scrate: &TokenStream2,
	traitinstance: &Ident,
	traittype: &syn::TypeParamBound,
	instance_opts: &InstanceOpts,
	cratename: &Ident,
	storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>,
	where_clause: &Option<WhereClause>,
) -> syn::Result<TokenStream2> {
	let mut impls = TokenStream2::new();

	let InstanceOpts {
		instance,
		default_instance,
		instantiable,
		..
	} = instance_opts;

	let build_prefix = |cratename, name| format!("{} {}", cratename, name);

	// Build Instantiable trait
	let mut const_names = vec![];

	for sline in storage_lines.inner.iter() {
		let DeclStorageLine {
			storage_type,
			name,
			..
		} = sline;

		let prefix = build_prefix(cratename, name);

		let type_infos = get_type_infos(storage_type);

		let const_name = syn::Ident::new(
			&format!("{}{}", impls::PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site()
		);
		const_names.push((const_name, String::new(), prefix.clone()));

		if let DeclStorageTypeInfosKind::Map { is_linked: true, .. } = type_infos.kind {
			let const_name = syn::Ident::new(
				&format!("{}{}", impls::HEAD_KEY_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			const_names.push((const_name, "head of ".into(), prefix));
		}
	}

	let instantiable = instantiable
		.clone()
		.unwrap_or_else(|| Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, Span::call_site()));

	// Declare Instance trait
	{
		let mut const_impls = TokenStream2::new();
		for (const_name, ..) in &const_names {
			const_impls.extend(quote! {
				const #const_name: &'static str;
			});
		}

		let hide = if instance.is_some() {
			quote!()
		} else {
			quote!(#[doc(hidden)])
		};

		impls.extend(quote! {
			/// Tag a type as an instance of a module.
			///
			/// Defines storage prefixes, they must be unique.
			#hide
			pub trait #instantiable: 'static {
				/// The prefix used by any storage entry of an instance.
				const PREFIX: &'static str;
				#const_impls
			}
		});
	}

	if instance.is_some() {
		let instances = (0..NUMBER_OF_INSTANCE)
			.map(|i| {
				let name = format!("Instance{}", i);
				let ident = Ident::new(&name, proc_macro2::Span::call_site());
				(name, ident, quote! {#[doc=r"Module instance"]})
			})
			.chain(
				default_instance
					.clone()
					.map(|ident|
						(String::new(), ident, quote! {#[doc=r"Default module instance"]})
					)
			);

		// Impl Instance trait for instances
		for (instance_prefix, ident, doc) in instances {
			impls.extend(
				create_and_impl_instance(
					&instance_prefix, &ident, &doc, &const_names, scrate, &instantiable, cratename
				)
			);
		}
	}

	// The name of the inherently available instance.
	let inherent_instance = Ident::new(INHERENT_INSTANCE_NAME, Span::call_site());

	if default_instance.is_some() {
		impls.extend(quote! {
			#[doc(hidden)]
			pub type #inherent_instance = #default_instance;
		});
	} else {
		impls.extend(
			create_and_impl_instance(
				"",
				&inherent_instance,
				&quote!(#[doc(hidden)]),
				&const_names,
				scrate,
				&instantiable,
				cratename,
			)
		);
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

		if type_infos.is_option && default_value.inner.is_some() {
			return Err(syn::Error::new_spanned(
				default_value,
				"Default values for Option types are not supported"
			));
		}

		let fielddefault = default_value.inner
			.as_ref()
			.map(|d| &d.expr)
			.map(|d| quote!( #d ))
			.unwrap_or_else(|| quote!{ Default::default() });
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
			fielddefault,
			prefix: build_prefix(cratename, name),
			name,
			attrs,
			where_clause,
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
				i.double_map(hasher.into_storage_hasher_struct(), key1_type, key2_type, key2_hasher.into_storage_hasher_struct())
			},
		};
		impls.extend(implementation)
	}

	Ok(impls)
}

fn decl_store_items(storage_lines: &ext::Punctuated<DeclStorageLine, Token![;]>) -> TokenStream2 {
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
	storage_lines.inner
		.iter()
		.fold(TokenStream2::new(), |mut items, line| {
			let name = &line.name;
			let type_infos = get_type_infos(&line.storage_type);
			let requires_trait = match type_infos.kind {
				DeclStorageTypeInfosKind::Simple => {
					ext::type_contains_ident(&type_infos.value_type, traitinstance)
				},
				DeclStorageTypeInfosKind::Map { key_type, .. } => {
					ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key_type, traitinstance)
				}
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key1_type, traitinstance)
						|| ext::type_contains_ident(key2_type, traitinstance)
				}
			};

			let struct_trait = if requires_trait {
				quote!(#traitinstance,)
			} else {
				quote!()
			};

			items.extend(
				quote!(
					type #name = #name<#struct_trait #instance>;
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
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance) {
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					quote!{
						#( #[ #attrs ] )*
						pub fn #get_fn() -> #value_type {
							<
								#name<#struct_trait #instance> as
								#scrate::storage::StorageValue<#typ>
							>::get()
						}
					}
				},
				DeclStorageTypeInfosKind::Map { key_type, is_linked, .. } => {
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key_type, traitinstance)
					{
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					let map = if is_linked {
						quote! { StorageLinkedMap }
					} else {
						quote! { StorageMap }
					};

					quote!{
						#( #[ #attrs ] )*
						pub fn #get_fn<K: #scrate::codec::EncodeLike<#key_type>>(key: K) -> #value_type {
							<
								#name<#struct_trait #instance> as
								#scrate::storage::#map<#key_type, #typ>
							>::get(key)
						}
					}
				}
				DeclStorageTypeInfosKind::DoubleMap { key1_type, key2_type, .. } => {
					let struct_trait = if ext::type_contains_ident(&type_infos.value_type, traitinstance)
						|| ext::type_contains_ident(key1_type, traitinstance)
						|| ext::type_contains_ident(key2_type, traitinstance)
					{
						quote!(#traitinstance,)
					} else {
						quote!()
					};

					quote!{
						pub fn #get_fn<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> #value_type
						where
							KArg1: #scrate::codec::EncodeLike<#key1_type>,
							KArg2: #scrate::codec::EncodeLike<#key2_type>,
						{
							<
								#name<#struct_trait #instance> as
								#scrate::storage::StorageDoubleMap<#key1_type, #key2_type, #typ>
							>::get(k1, k2)
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
	where_clause: &Option<WhereClause>,
	cratename: &Ident,
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
					#scrate::metadata::StorageEntryType::Plain(
						#scrate::metadata::DecodeDifferent::Encode(#styp),
					)
				}
			},
			DeclStorageTypeInfosKind::Map { key_type, is_linked, hasher } => {
				let hasher = hasher.into_metadata();
				let kty = clean_type_string(&quote!(#key_type).to_string());
				quote!{
					#scrate::metadata::StorageEntryType::Map {
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
				let k2_hasher = key2_hasher.into_metadata();
				quote!{
					#scrate::metadata::StorageEntryType::DoubleMap {
						hasher: #scrate::metadata::#hasher,
						key1: #scrate::metadata::DecodeDifferent::Encode(#k1ty),
						key2: #scrate::metadata::DecodeDifferent::Encode(#k2ty),
						value: #scrate::metadata::DecodeDifferent::Encode(#styp),
						key2_hasher: #scrate::metadata::#k2_hasher,
					}
				}
			},
		};
		let modifier = if type_infos.is_option {
			quote!{
				#scrate::metadata::StorageEntryModifier::Optional
			}
		} else {
			quote!{
				#scrate::metadata::StorageEntryModifier::Default
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
			#scrate::metadata::StorageEntryMetadata {
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
			pub struct #struct_name<
				#traitinstance, #instance #bound_instantiable #equal_default_instance
			>(pub #scrate::rstd::marker::PhantomData<(#traitinstance #comma_instance)>);

			#[cfg(feature = "std")]
			#[allow(non_upper_case_globals)]
			static #cache_name: #scrate::once_cell::sync::OnceCell<
				#scrate::rstd::vec::Vec<u8>
			> = #scrate::once_cell::sync::OnceCell::new();

			#[cfg(feature = "std")]
			impl<#traitinstance: #traittype, #instance #bound_instantiable> #scrate::metadata::DefaultByte
				for #struct_name<#traitinstance, #instance> #where_clause
			{
				fn default_byte(&self) -> #scrate::rstd::vec::Vec<u8> {
					use #scrate::codec::Encode;
					#cache_name.get_or_init(|| {
						let def_val: #value_type = #default;
						<#value_type as Encode>::encode(&def_val)
					}).clone()
				}
			}

			unsafe impl<#traitinstance: #traittype, #instance #bound_instantiable> Send
				for #struct_name<#traitinstance, #instance> #where_clause {}

			unsafe impl<#traitinstance: #traittype, #instance #bound_instantiable> Sync
				for #struct_name<#traitinstance, #instance> #where_clause {}

			#[cfg(not(feature = "std"))]
			impl<#traitinstance: #traittype, #instance #bound_instantiable> #scrate::metadata::DefaultByte
				for #struct_name<#traitinstance, #instance> #where_clause
			{
				fn default_byte(&self) -> #scrate::rstd::vec::Vec<u8> {
					use #scrate::codec::Encode;
					let def_val: #value_type = #default;
					<#value_type as Encode>::encode(&def_val)
				}
			}
		};

		default_getter_struct_def.extend(def_get);
	}

	let prefix = cratename.to_string();
	let prefix = instance.as_ref().map_or_else(|| quote!(#prefix), |i| quote!(#i::PREFIX));

	(default_getter_struct_def, quote!{
		#scrate::metadata::StorageMetadata {
			prefix: #scrate::metadata::DecodeDifferent::Encode(#prefix),
			entries: #scrate::metadata::DecodeDifferent::Encode(&[ #items ][..]),
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
		key2_hasher: HasherKind,
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
			key2_hasher: (&map.key2_hasher).into(),
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
	pub instance: Option<Ident>,
	pub default_instance: Option<Ident>,
	pub instantiable: Option<Ident>,
	pub comma_instance: TokenStream2,
	pub equal_default_instance: TokenStream2,
	pub bound_instantiable: TokenStream2,
}

fn get_instance_opts(
	instance: Option<Ident>,
	instantiable: Option<Ident>,
	default_instance: Option<Ident>,
) -> Result<InstanceOpts> {
	let right_syntax = "Should be $Instance: $Instantiable = $DefaultInstance";

	match (instance, instantiable, default_instance) {
		(Some(instance), Some(instantiable), default_instance) => {
			let (equal_default_instance, default_instance) = if let Some(def) = default_instance {
				(quote!{= #def}, Some(def))
			} else {
				(quote!(), None)
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
		(Some(instance), None, _) => Err(
			Error::new(
				instance.span(),
				format!(
					"Expect instantiable trait bound for instance: {}. {}",
					instance,
					right_syntax,
				)
			)
		),
		(None, Some(instantiable), _) => Err(
			Error::new(
				instantiable.span(),
				format!(
					"Expect instance generic for bound instantiable: {}. {}",
					instantiable,
					right_syntax,
				)
			)
		),
		(None, _, Some(default_instance)) => Err(
			Error::new(
				default_instance.span(),
				format!(
					"Expect instance generic for default instance: {}. {}",
					default_instance,
					right_syntax,
				)
			)
		),
	}
}
