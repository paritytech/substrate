// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Implementation of storage structures and implementation of storage traits on them.

use proc_macro2::{TokenStream, Ident, Span};
use quote::quote;
use super::{
	DeclStorageDefExt, StorageLineTypeDef,
	instance_trait::INHERENT_INSTANCE_NAME,
};

fn from_optional_value_to_query(is_option: bool, default: &Option<syn::Expr>) -> TokenStream {
	let default = default.as_ref().map(|d| quote!( #d ))
		.unwrap_or_else(|| quote!( Default::default() ));

	if !is_option {
		// raw type case
		quote!( v.unwrap_or_else(|| #default ) )
	} else {
		// Option<> type case
		quote!( v.or_else(|| #default ) )
	}
}

fn from_query_to_optional_value(is_option: bool) -> TokenStream {
	if !is_option {
		// raw type case
		quote!( Some(v) )
	} else {
		// Option<> type case
		quote!( v )
	}
}

pub fn decl_and_impl(def: &DeclStorageDefExt) -> TokenStream {
	let scrate = &def.hidden_crate;
	let mut impls = TokenStream::new();

	for line in &def.storage_lines {

		// Propagate doc attributes.
		let attrs = &line.doc_attrs;

		let visibility = &line.visibility;
		let optional_storage_runtime_comma = &line.optional_storage_runtime_comma;
		let optional_storage_runtime_bound_comma = &line.optional_storage_runtime_bound_comma;
		let optional_storage_where_clause = &line.optional_storage_where_clause;
		let optional_instance_bound_optional_default = &def.optional_instance_bound_optional_default;
		let optional_instance_bound = &def.optional_instance_bound;
		let optional_instance = &def.optional_instance;
		let name = &line.name;

		let struct_decl = quote!(
			#( #[ #attrs ] )*
			#visibility struct #name<
				#optional_storage_runtime_bound_comma #optional_instance_bound_optional_default
			>(
				#scrate::sp_std::marker::PhantomData<
					(#optional_storage_runtime_comma #optional_instance)
				>
			) #optional_storage_where_clause;
		);

		let from_query_to_optional_value = from_query_to_optional_value(line.is_option);
		let from_optional_value_to_query =
			from_optional_value_to_query(line.is_option, &line.default_value);

		// Contains accessor to instance, used to get prefixes
		let instance_or_inherent = if let Some(instance) = def.module_instance.as_ref() {
			instance.instance_generic.clone()
		} else {
			Ident::new(INHERENT_INSTANCE_NAME, Span::call_site())
		};

		let storage_name_bstr = syn::LitByteStr::new(
			line.name.to_string().as_ref(),
			line.name.span()
		);

		let storage_generator_trait = &line.storage_generator_trait;
		let storage_struct = &line.storage_struct;
		let impl_trait = quote!( #optional_storage_runtime_bound_comma #optional_instance_bound );
		let value_type = &line.value_type;
		let query_type = &line.query_type;

		let struct_impl = match &line.storage_type {
			StorageLineTypeDef::Simple(_) => {
				quote!(
					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;

						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}

						fn from_optional_value_to_query(v: Option<#value_type>) -> Self::Query {
							#from_optional_value_to_query
						}

						fn from_query_to_optional_value(v: Self::Query) -> Option<#value_type> {
							#from_query_to_optional_value
						}
					}
				)
			},
			StorageLineTypeDef::Map(map) => {
				let hasher = map.hasher.to_storage_hasher_struct();
				quote!(
					impl<#impl_trait> #scrate::storage::StoragePrefixedMap<#value_type>
						for #storage_struct #optional_storage_where_clause
					{
						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}
					}

					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;
						type Hasher = #scrate::#hasher;

						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}

						fn from_optional_value_to_query(v: Option<#value_type>) -> Self::Query {
							#from_optional_value_to_query
						}

						fn from_query_to_optional_value(v: Self::Query) -> Option<#value_type> {
							#from_query_to_optional_value
						}
					}
				)
			},
			StorageLineTypeDef::DoubleMap(map) => {
				let hasher1 = map.hasher1.to_storage_hasher_struct();
				let hasher2 = map.hasher2.to_storage_hasher_struct();
				quote!(
					impl<#impl_trait> #scrate::storage::StoragePrefixedMap<#value_type>
						for #storage_struct #optional_storage_where_clause
					{
						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}
					}

					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;

						type Hasher1 = #scrate::#hasher1;

						type Hasher2 = #scrate::#hasher2;

						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}

						fn from_optional_value_to_query(v: Option<#value_type>) -> Self::Query {
							#from_optional_value_to_query
						}

						fn from_query_to_optional_value(v: Self::Query) -> Option<#value_type> {
							#from_query_to_optional_value
						}
					}
				)
			},
			StorageLineTypeDef::NMap(_) => {
				quote!(
					impl<#impl_trait> #scrate::storage::StoragePrefixedMap<#value_type>
						for #storage_struct #optional_storage_where_clause
					{
						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}
					}

					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;

						fn module_prefix() -> &'static [u8] {
							<#instance_or_inherent as #scrate::traits::Instance>::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_bstr
						}

						fn from_optional_value_to_query(v: Option<#value_type>) -> Self::Query {
							#from_optional_value_to_query
						}

						fn from_query_to_optional_value(v: Self::Query) -> Option<#value_type> {
							#from_query_to_optional_value
						}
					}
				)
			}
		};

		let max_values = if let Some(max_values) = &line.max_values {
			quote::quote!({
				let max_values: u32 = (|| #max_values)();
				Some(max_values)
			})
		} else {
			quote::quote!(None)
		};

		let storage_info_impl = if def.generate_storage_info {
			match &line.storage_type {
				StorageLineTypeDef::Simple(_) => {
					quote!(
						impl<#impl_trait> #scrate::traits::StorageInfoTrait for #storage_struct
						#optional_storage_where_clause
						{
							fn storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								use #scrate::sp_runtime::SaturatedConversion;

								let max_size = <
									#value_type as #scrate::codec::MaxEncodedLen
								>::max_encoded_len()
									.saturated_into();

								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct as #scrate::#storage_generator_trait
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct as #scrate::#storage_generator_trait
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct as #scrate::#storage_generator_trait
										>::storage_value_final_key().to_vec(),
										max_values: Some(1),
										max_size: Some(max_size),
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::Map(map) => {
					let key = &map.key;
					quote!(
						impl<#impl_trait> #scrate::traits::StorageInfoTrait for #storage_struct
						#optional_storage_where_clause
						{
							fn storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								use #scrate::sp_runtime::SaturatedConversion;
								use #scrate::StorageHasher;

								let key_max_size = <
									Self as #scrate::storage::generator::StorageMap<_, _>
								>::Hasher::max_len::<#key>();

								let max_size = <
									#value_type as #scrate::codec::MaxEncodedLen
								>::max_encoded_len()
									.saturating_add(key_max_size)
									.saturated_into();

								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: Some(max_size),
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::DoubleMap(map) => {
					let key1 = &map.key1;
					let key2 = &map.key2;
					quote!(
						impl<#impl_trait> #scrate::traits::StorageInfoTrait for #storage_struct
						#optional_storage_where_clause
						{
							fn storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								use #scrate::sp_runtime::SaturatedConversion;
								use #scrate::StorageHasher;

								let key1_max_size = <
									Self as #scrate::storage::generator::StorageDoubleMap<_, _, _>
								>::Hasher1::max_len::<#key1>();

								let key2_max_size = <
									Self as #scrate::storage::generator::StorageDoubleMap<_, _, _>
								>::Hasher2::max_len::<#key2>();

								let max_size = <
									#value_type as #scrate::codec::MaxEncodedLen
								>::max_encoded_len()
									.saturating_add(key1_max_size)
									.saturating_add(key2_max_size)
									.saturated_into();

								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: Some(max_size),
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::NMap(map) => {
					let key = &map.to_keygen_struct(scrate);
					quote!(
						impl<#impl_trait> #scrate::traits::StorageInfoTrait for #storage_struct
						#optional_storage_where_clause
						{
							fn storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								use #scrate::sp_runtime::SaturatedConversion;

								let key_max_size = <
									#key as #scrate::storage::types::KeyGeneratorMaxEncodedLen
								>::key_max_encoded_len();

								let max_size = <
									#value_type as #scrate::codec::MaxEncodedLen
								>::max_encoded_len()
									.saturating_add(key_max_size)
									.saturated_into();

								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: Some(max_size),
									}
								]
							}
						}
					)
				},
			}
		} else {
			// Implement `__partial_storage_info` which doesn't require MaxEncodedLen on keys and
			// values.
			match &line.storage_type {
				StorageLineTypeDef::Simple(_) => {
					quote!(
						impl<#impl_trait> #scrate::traits::PartialStorageInfoTrait
						for #storage_struct
						#optional_storage_where_clause
						{
							fn partial_storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct as #scrate::#storage_generator_trait
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct as #scrate::#storage_generator_trait
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct as #scrate::#storage_generator_trait
										>::storage_value_final_key().to_vec(),
										max_values: Some(1),
										max_size: None,
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::Map(_) => {
					quote!(
						impl<#impl_trait> #scrate::traits::PartialStorageInfoTrait
						for #storage_struct
						#optional_storage_where_clause
						{
							fn partial_storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: None,
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::DoubleMap(_) => {
					quote!(
						impl<#impl_trait> #scrate::traits::PartialStorageInfoTrait
						for #storage_struct
						#optional_storage_where_clause
						{
							fn partial_storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: None,
									}
								]
							}
						}
					)
				},
				StorageLineTypeDef::NMap(_) => {
					quote!(
						impl<#impl_trait> #scrate::traits::PartialStorageInfoTrait
						for #storage_struct
						#optional_storage_where_clause
						{
							fn partial_storage_info()
								-> #scrate::sp_std::vec::Vec<#scrate::traits::StorageInfo>
							{
								#scrate::sp_std::vec![
									#scrate::traits::StorageInfo {
										pallet_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::module_prefix().to_vec(),
										storage_name: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::storage_prefix().to_vec(),
										prefix: <
											#storage_struct
											as #scrate::storage::StoragePrefixedMap<#value_type>
										>::final_prefix().to_vec(),
										max_values: #max_values,
										max_size: None,
									}
								]
							}
						}
					)
				},
			}
		};

		impls.extend(quote!(
			#struct_decl
			#struct_impl
			#storage_info_impl
		))
	}

	impls
}
