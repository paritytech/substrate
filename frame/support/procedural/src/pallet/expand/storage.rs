// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::pallet::{
	parse::storage::{Metadata, QueryKind, StorageDef, StorageGenerics},
	Def,
};
use quote::ToTokens;
use std::{collections::HashMap, ops::IndexMut};
use syn::spanned::Spanned;

/// Generate the prefix_ident related to the storage.
/// prefix_ident is used for the prefix struct to be given to storage as first generic param.
fn prefix_ident(storage: &StorageDef) -> syn::Ident {
	let storage_ident = &storage.ident;
	syn::Ident::new(&format!("_GeneratedPrefixForStorage{}", storage_ident), storage_ident.span())
}

/// Generate the counter_prefix_ident related to the storage.
/// counter_prefix_ident is used for the prefix struct to be given to counted storage map.
fn counter_prefix_ident(storage_ident: &syn::Ident) -> syn::Ident {
	syn::Ident::new(
		&format!("_GeneratedCounterPrefixForStorage{}", storage_ident),
		storage_ident.span(),
	)
}

/// Generate the counter_prefix related to the storage.
/// counter_prefix is used by counted storage map.
fn counter_prefix(prefix: &str) -> String {
	format!("CounterFor{}", prefix)
}

/// Check for duplicated storage prefixes. This step is necessary since users can specify an
/// alternative storage prefix using the #[pallet::storage_prefix] syntax, and we need to ensure
/// that the prefix specified by the user is not a duplicate of an existing one.
fn check_prefix_duplicates(
	storage_def: &StorageDef,
	// A hashmap of all already used prefix and their associated error if duplication
	used_prefixes: &mut HashMap<String, syn::Error>,
) -> syn::Result<()> {
	let prefix = storage_def.prefix();
	let dup_err = syn::Error::new(
		storage_def.prefix_span(),
		format!("Duplicate storage prefixes found for `{}`", prefix),
	);

	if let Some(other_dup_err) = used_prefixes.insert(prefix.clone(), dup_err.clone()) {
		let mut err = dup_err;
		err.combine(other_dup_err);
		return Err(err)
	}

	if let Metadata::CountedMap { .. } = storage_def.metadata {
		let counter_prefix = counter_prefix(&prefix);
		let counter_dup_err = syn::Error::new(
			storage_def.prefix_span(),
			format!(
				"Duplicate storage prefixes found for `{}`, used for counter associated to \
				counted storage map",
				counter_prefix,
			),
		);

		if let Some(other_dup_err) = used_prefixes.insert(counter_prefix, counter_dup_err.clone()) {
			let mut err = counter_dup_err;
			err.combine(other_dup_err);
			return Err(err)
		}
	}

	Ok(())
}

pub struct ResultOnEmptyStructMetadata {
	/// The Rust ident that is going to be used as the name of the OnEmpty struct.
	pub name: syn::Ident,
	/// The path to the error type being returned by the ResultQuery.
	pub error_path: syn::Path,
	/// The visibility of the OnEmpty struct.
	pub visibility: syn::Visibility,
	/// The type of the storage item.
	pub value_ty: syn::Type,
	/// The name of the pallet error enum variant that is going to be returned.
	pub variant_name: syn::Ident,
	/// The span used to report compilation errors about the OnEmpty struct.
	pub span: proc_macro2::Span,
}

///
/// * if generics are unnamed: replace the first generic `_` by the generated prefix structure
/// * if generics are named: reorder the generic, remove their name, and add the missing ones.
/// * Add `#[allow(type_alias_bounds)]`
pub fn process_generics(def: &mut Def) -> syn::Result<Vec<ResultOnEmptyStructMetadata>> {
	let frame_support = &def.frame_support;
	let mut on_empty_struct_metadata = Vec::new();

	for storage_def in def.storages.iter_mut() {
		let item = &mut def.item.content.as_mut().expect("Checked by def").1[storage_def.index];

		let typ_item = match item {
			syn::Item::Type(t) => t,
			_ => unreachable!("Checked by def"),
		};

		typ_item.attrs.push(syn::parse_quote!(#[allow(type_alias_bounds)]));

		let typ_path = match &mut *typ_item.ty {
			syn::Type::Path(p) => p,
			_ => unreachable!("Checked by def"),
		};

		let args = match &mut typ_path.path.segments[0].arguments {
			syn::PathArguments::AngleBracketed(args) => args,
			_ => unreachable!("Checked by def"),
		};

		let prefix_ident = prefix_ident(storage_def);
		let type_use_gen = if def.config.has_instance {
			quote::quote_spanned!(storage_def.attr_span => T, I)
		} else {
			quote::quote_spanned!(storage_def.attr_span => T)
		};

		let default_query_kind: syn::Type =
			syn::parse_quote!(#frame_support::storage::types::OptionQuery);
		let mut default_on_empty = |value_ty: syn::Type| -> syn::Type {
			if let Some(QueryKind::ResultQuery(error_path, variant_name)) =
				storage_def.query_kind.as_ref()
			{
				let on_empty_ident =
					quote::format_ident!("__Frame_Internal_Get{}Result", storage_def.ident);
				on_empty_struct_metadata.push(ResultOnEmptyStructMetadata {
					name: on_empty_ident.clone(),
					visibility: storage_def.vis.clone(),
					value_ty,
					error_path: error_path.clone(),
					variant_name: variant_name.clone(),
					span: storage_def.attr_span,
				});
				return syn::parse_quote!(#on_empty_ident)
			}
			syn::parse_quote!(#frame_support::traits::GetDefault)
		};
		let default_max_values: syn::Type = syn::parse_quote!(#frame_support::traits::GetDefault);

		let set_result_query_type_parameter = |query_type: &mut syn::Type| -> syn::Result<()> {
			if let Some(QueryKind::ResultQuery(error_path, _)) = storage_def.query_kind.as_ref() {
				if let syn::Type::Path(syn::TypePath { path: syn::Path { segments, .. }, .. }) =
					query_type
				{
					if let Some(seg) = segments.last_mut() {
						if let syn::PathArguments::AngleBracketed(
							syn::AngleBracketedGenericArguments { args, .. },
						) = &mut seg.arguments
						{
							args.clear();
							args.push(syn::GenericArgument::Type(syn::parse_quote!(#error_path)));
						}
					}
				} else {
					let msg = format!(
						"Invalid pallet::storage, unexpected type for query, expected ResultQuery \
						with 1 type parameter, found `{}`",
						query_type.to_token_stream().to_string()
					);
					return Err(syn::Error::new(query_type.span(), msg))
				}
			}
			Ok(())
		};

		if let Some(named_generics) = storage_def.named_generics.clone() {
			args.args.clear();
			args.args.push(syn::parse_quote!( #prefix_ident<#type_use_gen> ));
			match named_generics {
				StorageGenerics::Value { value, query_kind, on_empty } => {
					args.args.push(syn::GenericArgument::Type(value.clone()));
					let mut query_kind = query_kind.unwrap_or_else(|| default_query_kind.clone());
					set_result_query_type_parameter(&mut query_kind)?;
					args.args.push(syn::GenericArgument::Type(query_kind));
					let on_empty = on_empty.unwrap_or_else(|| default_on_empty(value));
					args.args.push(syn::GenericArgument::Type(on_empty));
				},
				StorageGenerics::Map { hasher, key, value, query_kind, on_empty, max_values } => {
					args.args.push(syn::GenericArgument::Type(hasher));
					args.args.push(syn::GenericArgument::Type(key));
					args.args.push(syn::GenericArgument::Type(value.clone()));
					let mut query_kind = query_kind.unwrap_or_else(|| default_query_kind.clone());
					set_result_query_type_parameter(&mut query_kind)?;
					args.args.push(syn::GenericArgument::Type(query_kind));
					let on_empty = on_empty.unwrap_or_else(|| default_on_empty(value));
					args.args.push(syn::GenericArgument::Type(on_empty));
					let max_values = max_values.unwrap_or_else(|| default_max_values.clone());
					args.args.push(syn::GenericArgument::Type(max_values));
				},
				StorageGenerics::CountedMap {
					hasher,
					key,
					value,
					query_kind,
					on_empty,
					max_values,
				} => {
					args.args.push(syn::GenericArgument::Type(hasher));
					args.args.push(syn::GenericArgument::Type(key));
					args.args.push(syn::GenericArgument::Type(value.clone()));
					let mut query_kind = query_kind.unwrap_or_else(|| default_query_kind.clone());
					set_result_query_type_parameter(&mut query_kind)?;
					args.args.push(syn::GenericArgument::Type(query_kind));
					let on_empty = on_empty.unwrap_or_else(|| default_on_empty(value));
					args.args.push(syn::GenericArgument::Type(on_empty));
					let max_values = max_values.unwrap_or_else(|| default_max_values.clone());
					args.args.push(syn::GenericArgument::Type(max_values));
				},
				StorageGenerics::DoubleMap {
					hasher1,
					key1,
					hasher2,
					key2,
					value,
					query_kind,
					on_empty,
					max_values,
				} => {
					args.args.push(syn::GenericArgument::Type(hasher1));
					args.args.push(syn::GenericArgument::Type(key1));
					args.args.push(syn::GenericArgument::Type(hasher2));
					args.args.push(syn::GenericArgument::Type(key2));
					args.args.push(syn::GenericArgument::Type(value.clone()));
					let mut query_kind = query_kind.unwrap_or_else(|| default_query_kind.clone());
					set_result_query_type_parameter(&mut query_kind)?;
					args.args.push(syn::GenericArgument::Type(query_kind));
					let on_empty = on_empty.unwrap_or_else(|| default_on_empty(value));
					args.args.push(syn::GenericArgument::Type(on_empty));
					let max_values = max_values.unwrap_or_else(|| default_max_values.clone());
					args.args.push(syn::GenericArgument::Type(max_values));
				},
				StorageGenerics::NMap { keygen, value, query_kind, on_empty, max_values } => {
					args.args.push(syn::GenericArgument::Type(keygen));
					args.args.push(syn::GenericArgument::Type(value.clone()));
					let mut query_kind = query_kind.unwrap_or_else(|| default_query_kind.clone());
					set_result_query_type_parameter(&mut query_kind)?;
					args.args.push(syn::GenericArgument::Type(query_kind));
					let on_empty = on_empty.unwrap_or_else(|| default_on_empty(value));
					args.args.push(syn::GenericArgument::Type(on_empty));
					let max_values = max_values.unwrap_or_else(|| default_max_values.clone());
					args.args.push(syn::GenericArgument::Type(max_values));
				},
			}
		} else {
			args.args[0] = syn::parse_quote!( #prefix_ident<#type_use_gen> );

			let (value_idx, query_idx, on_empty_idx) = match storage_def.metadata {
				Metadata::Value { .. } => (1, 2, 3),
				Metadata::NMap { .. } => (2, 3, 4),
				Metadata::Map { .. } | Metadata::CountedMap { .. } => (3, 4, 5),
				Metadata::DoubleMap { .. } => (5, 6, 7),
			};

			if query_idx < args.args.len() {
				if let syn::GenericArgument::Type(query_kind) = args.args.index_mut(query_idx) {
					set_result_query_type_parameter(query_kind)?;
				}
			} else if let Some(QueryKind::ResultQuery(error_path, _)) =
				storage_def.query_kind.as_ref()
			{
				args.args.push(syn::GenericArgument::Type(syn::parse_quote!(#error_path)))
			}

			// Here, we only need to check if OnEmpty is *not* specified, and if so, then we have to
			// generate a default OnEmpty struct for it.
			if on_empty_idx >= args.args.len() &&
				matches!(storage_def.query_kind.as_ref(), Some(QueryKind::ResultQuery(_, _)))
			{
				let value_ty = match args.args[value_idx].clone() {
					syn::GenericArgument::Type(ty) => ty,
					_ => unreachable!(),
				};
				let on_empty = default_on_empty(value_ty);
				args.args.push(syn::GenericArgument::Type(on_empty));
			}
		}
	}

	Ok(on_empty_struct_metadata)
}

///
/// * generate StoragePrefix structs (e.g. for a storage `MyStorage` a struct with the name
///   `_GeneratedPrefixForStorage$NameOfStorage` is generated) and implements StorageInstance trait.
/// * if generics are unnamed: replace the first generic `_` by the generated prefix structure
/// * if generics are named: reorder the generic, remove their name, and add the missing ones.
/// * Add `#[allow(type_alias_bounds)]` on storages type alias
/// * generate metadatas
pub fn expand_storages(def: &mut Def) -> proc_macro2::TokenStream {
	let on_empty_struct_metadata = match process_generics(def) {
		Ok(idents) => idents,
		Err(e) => return e.into_compile_error(),
	};

	// Check for duplicate prefixes
	let mut prefix_set = HashMap::new();
	let mut errors = def
		.storages
		.iter()
		.filter_map(|storage_def| check_prefix_duplicates(storage_def, &mut prefix_set).err());
	if let Some(mut final_error) = errors.next() {
		errors.for_each(|error| final_error.combine(error));
		return final_error.into_compile_error()
	}

	let frame_support = &def.frame_support;
	let frame_system = &def.frame_system;
	let pallet_ident = &def.pallet_struct.pallet;

	let entries_builder = def.storages.iter().map(|storage| {
		let no_docs = vec![];
		let docs = if cfg!(feature = "no-metadata-docs") { &no_docs } else { &storage.docs };

		let ident = &storage.ident;
		let gen = &def.type_use_generics(storage.attr_span);
		let full_ident = quote::quote_spanned!(storage.attr_span => #ident<#gen> );

		let cfg_attrs = &storage.cfg_attrs;

		quote::quote_spanned!(storage.attr_span =>
			#(#cfg_attrs)*
			{
				<#full_ident as #frame_support::storage::StorageEntryMetadataBuilder>::build_metadata(
					#frame_support::sp_std::vec![
						#( #docs, )*
					],
					&mut entries,
				);
			}
		)
	});

	let getters = def.storages.iter().map(|storage| {
		if let Some(getter) = &storage.getter {
			let completed_where_clause =
				super::merge_where_clauses(&[&storage.where_clause, &def.config.where_clause]);
			let docs = storage
				.docs
				.iter()
				.map(|d| quote::quote_spanned!(storage.attr_span => #[doc = #d]));

			let ident = &storage.ident;
			let gen = &def.type_use_generics(storage.attr_span);
			let type_impl_gen = &def.type_impl_generics(storage.attr_span);
			let type_use_gen = &def.type_use_generics(storage.attr_span);
			let full_ident = quote::quote_spanned!(storage.attr_span => #ident<#gen> );

			let cfg_attrs = &storage.cfg_attrs;

			match &storage.metadata {
				Metadata::Value { value } => {
					let query = match storage.query_kind.as_ref().expect("Checked by def") {
						QueryKind::OptionQuery => quote::quote_spanned!(storage.attr_span =>
							Option<#value>
						),
						QueryKind::ResultQuery(error_path, _) =>
							quote::quote_spanned!(storage.attr_span =>
								Result<#value, #error_path>
							),
						QueryKind::ValueQuery => quote::quote!(#value),
					};
					quote::quote_spanned!(storage.attr_span =>
						#(#cfg_attrs)*
						impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
							#( #docs )*
							pub fn #getter() -> #query {
								<
									#full_ident as #frame_support::storage::StorageValue<#value>
								>::get()
							}
						}
					)
				},
				Metadata::Map { key, value } => {
					let query = match storage.query_kind.as_ref().expect("Checked by def") {
						QueryKind::OptionQuery => quote::quote_spanned!(storage.attr_span =>
							Option<#value>
						),
						QueryKind::ResultQuery(error_path, _) =>
							quote::quote_spanned!(storage.attr_span =>
								Result<#value, #error_path>
							),
						QueryKind::ValueQuery => quote::quote!(#value),
					};
					quote::quote_spanned!(storage.attr_span =>
						#(#cfg_attrs)*
						impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
							#( #docs )*
							pub fn #getter<KArg>(k: KArg) -> #query where
								KArg: #frame_support::codec::EncodeLike<#key>,
							{
								<
									#full_ident as #frame_support::storage::StorageMap<#key, #value>
								>::get(k)
							}
						}
					)
				},
				Metadata::CountedMap { key, value } => {
					let query = match storage.query_kind.as_ref().expect("Checked by def") {
						QueryKind::OptionQuery => quote::quote_spanned!(storage.attr_span =>
							Option<#value>
						),
						QueryKind::ResultQuery(error_path, _) =>
							quote::quote_spanned!(storage.attr_span =>
								Result<#value, #error_path>
							),
						QueryKind::ValueQuery => quote::quote!(#value),
					};
					quote::quote_spanned!(storage.attr_span =>
						#(#cfg_attrs)*
						impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
							#( #docs )*
							pub fn #getter<KArg>(k: KArg) -> #query where
								KArg: #frame_support::codec::EncodeLike<#key>,
							{
								// NOTE: we can't use any trait here because CountedStorageMap
								// doesn't implement any.
								<#full_ident>::get(k)
							}
						}
					)
				},
				Metadata::DoubleMap { key1, key2, value } => {
					let query = match storage.query_kind.as_ref().expect("Checked by def") {
						QueryKind::OptionQuery => quote::quote_spanned!(storage.attr_span =>
							Option<#value>
						),
						QueryKind::ResultQuery(error_path, _) =>
							quote::quote_spanned!(storage.attr_span =>
								Result<#value, #error_path>
							),
						QueryKind::ValueQuery => quote::quote!(#value),
					};
					quote::quote_spanned!(storage.attr_span =>
						#(#cfg_attrs)*
						impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
							#( #docs )*
							pub fn #getter<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> #query where
								KArg1: #frame_support::codec::EncodeLike<#key1>,
								KArg2: #frame_support::codec::EncodeLike<#key2>,
							{
								<
									#full_ident as
									#frame_support::storage::StorageDoubleMap<#key1, #key2, #value>
								>::get(k1, k2)
							}
						}
					)
				},
				Metadata::NMap { keygen, value, .. } => {
					let query = match storage.query_kind.as_ref().expect("Checked by def") {
						QueryKind::OptionQuery => quote::quote_spanned!(storage.attr_span =>
							Option<#value>
						),
						QueryKind::ResultQuery(error_path, _) =>
							quote::quote_spanned!(storage.attr_span =>
								Result<#value, #error_path>
							),
						QueryKind::ValueQuery => quote::quote!(#value),
					};
					quote::quote_spanned!(storage.attr_span =>
						#(#cfg_attrs)*
						impl<#type_impl_gen> #pallet_ident<#type_use_gen> #completed_where_clause {
							#( #docs )*
							pub fn #getter<KArg>(key: KArg) -> #query
							where
								KArg: #frame_support::storage::types::EncodeLikeTuple<
									<#keygen as #frame_support::storage::types::KeyGenerator>::KArg
								>
									+ #frame_support::storage::types::TupleToEncodedIter,
							{
								<
									#full_ident as
									#frame_support::storage::StorageNMap<#keygen, #value>
								>::get(key)
							}
						}
					)
				},
			}
		} else {
			Default::default()
		}
	});

	let prefix_structs = def.storages.iter().map(|storage_def| {
		let type_impl_gen = &def.type_impl_generics(storage_def.attr_span);
		let type_use_gen = &def.type_use_generics(storage_def.attr_span);
		let prefix_struct_ident = prefix_ident(storage_def);
		let prefix_struct_vis = &storage_def.vis;
		let prefix_struct_const = storage_def.prefix();
		let config_where_clause = &def.config.where_clause;

		let cfg_attrs = &storage_def.cfg_attrs;

		let maybe_counter = if let Metadata::CountedMap { .. } = storage_def.metadata {
			let counter_prefix_struct_ident = counter_prefix_ident(&storage_def.ident);
			let counter_prefix_struct_const = counter_prefix(&prefix_struct_const);

			quote::quote_spanned!(storage_def.attr_span =>
				#(#cfg_attrs)*
				#[doc(hidden)]
				#prefix_struct_vis struct #counter_prefix_struct_ident<#type_use_gen>(
					core::marker::PhantomData<(#type_use_gen,)>
				);
				#(#cfg_attrs)*
				impl<#type_impl_gen> #frame_support::traits::StorageInstance
					for #counter_prefix_struct_ident<#type_use_gen>
					#config_where_clause
				{
					fn pallet_prefix() -> &'static str {
						<
							<T as #frame_system::Config>::PalletInfo
							as #frame_support::traits::PalletInfo
						>::name::<Pallet<#type_use_gen>>()
							.expect("No name found for the pallet in the runtime! This usually means that the pallet wasn't added to `construct_runtime!`.")
					}
					const STORAGE_PREFIX: &'static str = #counter_prefix_struct_const;
				}
				#(#cfg_attrs)*
				impl<#type_impl_gen> #frame_support::storage::types::CountedStorageMapInstance
					for #prefix_struct_ident<#type_use_gen>
					#config_where_clause
				{
					type CounterPrefix = #counter_prefix_struct_ident<#type_use_gen>;
				}
			)
		} else {
			proc_macro2::TokenStream::default()
		};

		quote::quote_spanned!(storage_def.attr_span =>
			#maybe_counter

			#(#cfg_attrs)*
			#[doc(hidden)]
			#prefix_struct_vis struct #prefix_struct_ident<#type_use_gen>(
				core::marker::PhantomData<(#type_use_gen,)>
			);
			#(#cfg_attrs)*
			impl<#type_impl_gen> #frame_support::traits::StorageInstance
				for #prefix_struct_ident<#type_use_gen>
				#config_where_clause
			{
				fn pallet_prefix() -> &'static str {
					<
						<T as #frame_system::Config>::PalletInfo
						as #frame_support::traits::PalletInfo
					>::name::<Pallet<#type_use_gen>>()
						.expect("No name found for the pallet in the runtime! This usually means that the pallet wasn't added to `construct_runtime!`.")
				}
				const STORAGE_PREFIX: &'static str = #prefix_struct_const;
			}
		)
	});

	let on_empty_structs = on_empty_struct_metadata.into_iter().map(|metadata| {
		use crate::pallet::parse::GenericKind;
		use syn::{GenericArgument, Path, PathArguments, PathSegment, Type, TypePath};

		let ResultOnEmptyStructMetadata {
			name,
			visibility,
			value_ty,
			error_path,
			variant_name,
			span,
		} = metadata;

		let generic_kind = match error_path.segments.last() {
			Some(PathSegment { arguments: PathArguments::AngleBracketed(args), .. }) => {
				let (has_config, has_instance) =
					args.args.iter().fold((false, false), |(has_config, has_instance), arg| {
						match arg {
							GenericArgument::Type(Type::Path(TypePath {
								path: Path { segments, .. },
								..
							})) => {
								let maybe_config =
									segments.first().map_or(false, |seg| seg.ident == "T");
								let maybe_instance =
									segments.first().map_or(false, |seg| seg.ident == "I");

								(has_config || maybe_config, has_instance || maybe_instance)
							},
							_ => (has_config, has_instance),
						}
					});
				GenericKind::from_gens(has_config, has_instance).unwrap_or(GenericKind::None)
			},
			_ => GenericKind::None,
		};
		let type_impl_gen = generic_kind.type_impl_gen(proc_macro2::Span::call_site());
		let config_where_clause = &def.config.where_clause;

		quote::quote_spanned!(span =>
			#[doc(hidden)]
			#[allow(non_camel_case_types)]
			#visibility struct #name;

			impl<#type_impl_gen> #frame_support::traits::Get<Result<#value_ty, #error_path>>
				for #name
				#config_where_clause
			{
				fn get() -> Result<#value_ty, #error_path> {
					Err(<#error_path>::#variant_name)
				}
			}
		)
	});

	let mut where_clauses = vec![&def.config.where_clause];
	where_clauses.extend(def.storages.iter().map(|storage| &storage.where_clause));
	let completed_where_clause = super::merge_where_clauses(&where_clauses);
	let type_impl_gen = &def.type_impl_generics(proc_macro2::Span::call_site());
	let type_use_gen = &def.type_use_generics(proc_macro2::Span::call_site());

	quote::quote!(
		impl<#type_impl_gen> #pallet_ident<#type_use_gen>
			#completed_where_clause
		{
			#[doc(hidden)]
			pub fn storage_metadata() -> #frame_support::metadata::PalletStorageMetadata {
				#frame_support::metadata::PalletStorageMetadata {
					prefix: <
						<T as #frame_system::Config>::PalletInfo as
						#frame_support::traits::PalletInfo
					>::name::<#pallet_ident<#type_use_gen>>()
						.expect("No name found for the pallet in the runtime! This usually means that the pallet wasn't added to `construct_runtime!`."),
					entries: {
						#[allow(unused_mut)]
						let mut entries = #frame_support::sp_std::vec![];
						#( #entries_builder )*
						entries
					},
				}
			}
		}

		#( #getters )*
		#( #prefix_structs )*
		#( #on_empty_structs )*
	)
}
