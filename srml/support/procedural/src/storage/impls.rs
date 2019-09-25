// Copyright 2019 Parity Technologies (UK) Ltd.
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

use crate::storage::transformation::{DeclStorageTypeInfos, InstanceOpts};

use srml_support_procedural_tools::syn_ext as ext;
use proc_macro2::TokenStream as TokenStream2;
use syn::Ident;
use quote::quote;

fn from_optional_value_to_query(is_option: bool, fielddefault: TokenStream2) -> TokenStream2 {
	if !is_option {
		// raw type case
		quote!( v.unwrap_or_else(|| #fielddefault ) )
	} else {
		// Option<> type case
		quote!( v.or_else(|| #fielddefault ) )
	}
}

fn from_query_to_optional_value(is_option: bool) -> TokenStream2 {
	if !is_option {
		// raw type case
		quote!( Some(v) )
	} else {
		// Option<> type case
		quote!( v )
	}
}

// prefix for consts in trait Instance
pub(crate) const PREFIX_FOR: &str = "PREFIX_FOR_";
pub(crate) const HEAD_KEY_FOR: &str = "HEAD_KEY_FOR_";

pub(crate) struct Impls<'a, I: Iterator<Item=syn::Meta>> {
	pub scrate: &'a TokenStream2,
	pub visibility: &'a syn::Visibility,
	pub traitinstance: &'a syn::Ident,
	pub traittype: &'a syn::TypeParamBound,
	pub instance_opts: &'a InstanceOpts,
	pub type_infos: DeclStorageTypeInfos<'a>,
	pub fielddefault: TokenStream2,
	pub prefix: String,
	pub cratename: &'a syn::Ident,
	pub name: &'a syn::Ident,
	pub attrs: I,
	pub where_clause: &'a Option<syn::WhereClause>,
}

impl<'a, I: Iterator<Item=syn::Meta>> Impls<'a, I> {
	pub fn simple_value(self) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;

		let from_optional_value_to_query = from_optional_value_to_query(is_option, fielddefault);
		let from_query_to_optional_value = from_query_to_optional_value(is_option);

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site());
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if ext::type_contains_ident(
			value_type, traitinstance
		) {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for value
		quote! {
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::generator::StorageValue<#typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				fn unhashed_key() -> &'static [u8] {
					#final_prefix
				}

				fn from_optional_value_to_query(v: Option<#typ>) -> Self::Query {
					#from_optional_value_to_query
				}

				fn from_query_to_optional_value(v: Self::Query) -> Option<#typ> {
					#from_query_to_optional_value
				}
			}
		}
	}

	pub fn map(self, hasher: TokenStream2, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;

		let from_optional_value_to_query = from_optional_value_to_query(is_option, fielddefault);
		let from_query_to_optional_value = from_query_to_optional_value(is_option);

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = syn::Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()),
				proc_macro2::Span::call_site(),
			);
			quote! { #instance::#const_name.as_bytes() }
		} else {
			quote! { #prefix.as_bytes() }
		};

		let trait_required = ext::type_contains_ident(value_type, traitinstance)
			|| ext::type_contains_ident(kty, traitinstance);

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if trait_required {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for map
		quote!{
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::generator::StorageMap<#kty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;
				type Hasher = #scrate::#hasher;

				fn prefix() -> &'static [u8] {
					#final_prefix
				}

				fn from_optional_value_to_query(v: Option<#typ>) -> Self::Query {
					#from_optional_value_to_query
				}

				fn from_query_to_optional_value(v: Self::Query) -> Option<#typ> {
					#from_query_to_optional_value
				}
			}
		}
	}

	pub fn linked_map(self, hasher: TokenStream2, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		// make sure to use different prefix for head and elements.
		let head_key = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", HEAD_KEY_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			let head_key = format!("head of {}", prefix);
			quote!{ #head_key.as_bytes() }
		};

		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;

		let from_optional_value_to_query = from_optional_value_to_query(is_option, fielddefault);
		let from_query_to_optional_value = from_query_to_optional_value(is_option);

		let trait_required = ext::type_contains_ident(value_type, traitinstance)
			|| ext::type_contains_ident(kty, traitinstance);

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if trait_required {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for linked map
		quote! {
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::generator::StorageLinkedMap<#kty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;
				type Hasher = #scrate::#hasher;

				fn prefix() -> &'static [u8] {
					#final_prefix
				}

				fn head_key() -> &'static [u8] {
					#head_key
				}

				fn from_optional_value_to_query(v: Option<#typ>) -> Self::Query {
					#from_optional_value_to_query
				}

				fn from_query_to_optional_value(v: Self::Query) -> Option<#typ> {
					#from_query_to_optional_value
				}
			}
		}
	}

	pub fn double_map(
		self,
		hasher: TokenStream2,
		k1ty: &syn::Type,
		k2ty: &syn::Type,
		k2_hasher: TokenStream2,
	) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			instance_opts,
			where_clause,
			..
		} = self;

		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;

		let from_optional_value_to_query = from_optional_value_to_query(is_option, fielddefault);
		let from_query_to_optional_value = from_query_to_optional_value(is_option);

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if ext::type_contains_ident(
			value_type, traitinstance
		) || ext::type_contains_ident(k1ty, traitinstance) || ext::type_contains_ident(k2ty, traitinstance)
		{
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for double map
		quote!{
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait> (
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::generator::StorageDoubleMap<#k1ty, #k2ty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				type Hasher1 = #scrate::#hasher;

				type Hasher2 = #scrate::#k2_hasher;

				fn key1_prefix() -> &'static [u8] {
					#final_prefix
				}

				fn from_optional_value_to_query(v: Option<#typ>) -> Self::Query {
					#from_optional_value_to_query
				}

				fn from_query_to_optional_value(v: Self::Query) -> Option<#typ> {
					#from_query_to_optional_value
				}
			}
		}
	}
}
