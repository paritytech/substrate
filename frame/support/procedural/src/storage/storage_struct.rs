// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

pub fn decl_and_impl(scrate: &TokenStream, def: &DeclStorageDefExt) -> TokenStream {
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

		let storage_name_str = syn::LitStr::new(&line.name.to_string(), line.name.span());

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
							#instance_or_inherent::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_str.as_bytes()
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
							#instance_or_inherent::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_str.as_bytes()
						}
					}

					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;
						type Hasher = #scrate::#hasher;

						fn module_prefix() -> &'static [u8] {
							#instance_or_inherent::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_str.as_bytes()
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
							#instance_or_inherent::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_str.as_bytes()
						}
					}

					impl<#impl_trait> #scrate::#storage_generator_trait for #storage_struct
					#optional_storage_where_clause
					{
						type Query = #query_type;

						type Hasher1 = #scrate::#hasher1;

						type Hasher2 = #scrate::#hasher2;

						fn module_prefix() -> &'static [u8] {
							#instance_or_inherent::PREFIX.as_bytes()
						}

						fn storage_prefix() -> &'static [u8] {
							#storage_name_str.as_bytes()
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

		impls.extend(quote!(
			#struct_decl
			#struct_impl
		))
	}

	impls
}
