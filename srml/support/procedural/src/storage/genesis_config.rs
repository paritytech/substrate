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

use srml_support_procedural_tools::syn_ext as ext;
use proc_macro2::TokenStream as TokenStream2;

use syn::{WhereClause, spanned::Spanned};
use quote::{quote, quote_spanned};

use super::instance_trait::DEFAULT_INSTANTIABLE_TRAIT_NAME;

const DEFAULT_INSTANCE_NAME: &str = "__GeneratedInstance";

pub fn impl_genesis_config(scrate: &TokenStream2, def: &super::DeclStorageDefExt) -> TokenStream2 {
	let mut is_trait_needed = false;
	let mut serde_complete_bound = Vec::new();
	let mut config_fields = TokenStream2::new();
	let mut config_field_default = TokenStream2::new();
	let mut builders = TokenStream2::new();
	let mut assimilate_require_generic = def.module_instance.is_some();
	let mut builders_clone_bound = Vec::new();

	for line in def.storage_lines.iter() {
		let opt_build = line.build.as_ref()
			.map(|b| {
				assimilate_require_generic |= ext::expr_contains_ident(&b, &def.module_runtime_generic);
				quote!( #b )
			});

		// need build line
		let builder = if let Some(config_field) = &line.config {
			is_trait_needed |= line.is_generic_over_runtime;

			if opt_build.is_none() {
				builders_clone_bound.push(line.query_type.clone());
			}

			let query_type = &line.query_type;
			serde_complete_bound.push(quote!( #query_type ));
			let value_type = &line.value_type;
			if line.is_option {
				serde_complete_bound.push(value_type.clone());
			}

			// Propagate doc attributes.
			let attrs = &line.doc_attrs;

			match &line.storage_type {
				super::StorageLineTypeDef::Simple(_) => {
					config_fields.extend(
						quote!( #( #[ #attrs ] )* pub #config_field: #value_type, )
					);
				},
				super::StorageLineTypeDef::Map(map)
					| super::StorageLineTypeDef::LinkedMap(map)
				=> {
					let key = &map.key;
					serde_complete_bound.push(quote!( #key ));

					if opt_build.is_none() {
						builders_clone_bound.push(key.clone());
					}

					config_fields.extend(
						quote!( #( #[ #attrs ] )* pub #config_field: Vec<(#key, #value_type)>, )
					);
				},
				super::StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;
					serde_complete_bound.push(quote!( #key1 ));
					serde_complete_bound.push(quote!( #key2 ));

					if opt_build.is_none() {
						builders_clone_bound.push(key1.clone());
						builders_clone_bound.push(key2.clone());
					}

					config_fields.extend(
						quote!( #( #[ #attrs ] )* pub #config_field: Vec<(#key1, #key2, #value_type)>, )
					);
				},
			}

			let fielddefault = line.default_value.as_ref()
				.map(|d| {
					if line.is_option {
						quote!( #d.unwrap_or_default() )
					} else {
						quote!( #d )
					}
				})
				.unwrap_or_else(|| quote!( Default::default() ));

			config_field_default.extend(quote!( #config_field: #fielddefault, ));

			opt_build.or_else(|| Some(quote!( (|config: &Self| config.#config_field.clone()) )))
		} else {
			opt_build
		};

		let value_type = &line.value_type;
		if let Some(builder) = builder {
			assimilate_require_generic |= line.is_generic_over_runtime;
			let storage_struct = &line.storage_struct;
			let storage_trait = &line.storage_trait;
			builders.extend(match &line.storage_type {
				super::StorageLineTypeDef::Simple(_) => {
					quote!{{
						let v = (#builder)(&self);
						<#storage_struct as #scrate::#storage_trait>::put::<#value_type>(v);
					}}
				},
				super::StorageLineTypeDef::Map(map)
					| super::StorageLineTypeDef::LinkedMap(map)
				=> {
					let key = &map.key;
					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<#key, #value_type>(k, v);
						});
					}}
				},
				super::StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;
					quote!{{
						let data = (#builder)(&self);
						data.into_iter().for_each(|(k1, k2, v)| {
							<#storage_struct as #scrate::#storage_trait>::insert::<
								#key1, #key2, #value_type
							>(k1, k2, v);
						});
					}}
				},
			});
		}
	}

	// extra genesis build
	let scall = def.extra_genesis_build.as_ref().map(|expr| {
		assimilate_require_generic |= ext::expr_contains_ident(&expr, &def.module_runtime_generic);
		quote_spanned! { expr.span() =>
			let scall: fn(&Self) = #expr; scall
		}
	}).unwrap_or_else(|| quote!{ let scall: fn(&Self) = |_| {}; scall });

	// extra genesis fields
	let mut genesis_extrafields = TokenStream2::new();
	let mut genesis_extrafields_default = TokenStream2::new();

	for line in &def.extra_genesis_config_lines {
		let extra_type = &line.typ;
		let extra_field = &line.name;

		is_trait_needed |= ext::type_contains_ident(extra_type, &def.module_runtime_generic);

		serde_complete_bound.push(quote!( #extra_type ));

		// Propagate doc attributes.
		let attrs = line.attrs.iter()
			.filter_map(|a| a.parse_meta().ok())
			.filter(|m| m.name() == "doc");

		genesis_extrafields.extend(quote!{
			#( #[ #attrs ] )* pub #extra_field: #extra_type,
		});

		let extra_default = line.default.as_ref().map(|e| quote!{ #e })
			.unwrap_or_else(|| quote!( Default::default() ));

		genesis_extrafields_default.extend(quote!{
			#extra_field: #extra_default,
		});
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

	let is_extra_genesis_needed = def.extra_genesis_build.is_some()
		|| !config_fields.is_empty()
		|| !genesis_extrafields.is_empty()
		|| !builders.is_empty();

	if is_extra_genesis_needed {
		let runtime_generic = &def.module_runtime_generic;
		let runtime_trait = &def.module_runtime_trait;
		let optional_instance = &def.optional_instance;
		let optional_instance_bound = &def.optional_instance_bound;
		let optional_instance_bound_optional_default = &def.optional_instance_bound_optional_default;
		let where_clause = &def.where_clause;

		let inherent_instance = def.optional_instance.clone().unwrap_or_else(|| {
			let name = syn::Ident::new(DEFAULT_INSTANCE_NAME, proc_macro2::Span::call_site());
			quote!( #name )
		});
		let inherent_instance_bound = def.optional_instance_bound.clone().unwrap_or_else(|| {
			let bound = syn::Ident::new(DEFAULT_INSTANTIABLE_TRAIT_NAME, proc_macro2::Span::call_site());
			quote!( #inherent_instance: #bound )
		});

		let build_storage_impl = quote!(
			<#runtime_generic: #runtime_trait, #inherent_instance_bound>
		);
		let (fparam_struct, fparam_impl, sparam) = if is_trait_needed {
			(
				quote!(<#runtime_generic: #runtime_trait, #optional_instance_bound_optional_default>),
				quote!(<#runtime_generic: #runtime_trait, #optional_instance_bound>),
				quote!(<#runtime_generic, #optional_instance>),
			)
		} else {
			// do not even need type parameter
			(
				quote!(),
				quote!(),
				quote!(),
			)
		};

		let (fn_generic, fn_traitinstance) = if !is_trait_needed && assimilate_require_generic {
			(
				quote!( <#runtime_generic: #runtime_trait, #optional_instance_bound> ),
				quote!( #runtime_generic, #optional_instance )
			)
		} else {
			(quote!(), quote!())
		};

		let impl_trait = quote!(BuildModuleGenesisStorage<#runtime_generic, #inherent_instance>);

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

		quote!{
			#[derive(#scrate::Serialize, #scrate::Deserialize)]
			#[cfg(feature = "std")]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			#serde_bug_bound
			pub struct GenesisConfig#fparam_struct #genesis_where_clause {
				#config_fields
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
		}
	} else {
		quote!()
	}
}
