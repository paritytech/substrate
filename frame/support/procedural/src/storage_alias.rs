// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Implementation of the `storage_alias` attribute macro.

use crate::counter_prefix;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
	parenthesized,
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	spanned::Spanned,
	token,
	visit::Visit,
	Attribute, Error, Ident, Result, Token, Type, TypeParam, Visibility, WhereClause,
};

/// Extension trait for [`Type`].
trait TypeExt {
	fn get_ident(&self) -> Option<&Ident>;
	fn contains_ident(&self, ident: &Ident) -> bool;
}

impl TypeExt for Type {
	fn get_ident(&self) -> Option<&Ident> {
		match self {
			Type::Path(p) => match &p.qself {
				Some(qself) => qself.ty.get_ident(),
				None => p.path.get_ident(),
			},
			_ => None,
		}
	}

	fn contains_ident(&self, ident: &Ident) -> bool {
		struct ContainsIdent<'a> {
			ident: &'a Ident,
			found: bool,
		}
		impl<'a, 'ast> Visit<'ast> for ContainsIdent<'a> {
			fn visit_ident(&mut self, i: &'ast Ident) {
				if i == self.ident {
					self.found = true;
				}
			}
		}

		let mut visitor = ContainsIdent { ident, found: false };
		syn::visit::visit_type(&mut visitor, self);
		visitor.found
	}
}

/// Represents generics which only support [`TypeParam`] separated by commas.
struct SimpleGenerics {
	lt_token: Token![<],
	params: Punctuated<TypeParam, token::Comma>,
	gt_token: Token![>],
}

impl SimpleGenerics {
	/// Returns the generics for types declarations etc.
	fn type_generics(&self) -> impl Iterator<Item = &Ident> {
		self.params.iter().map(|p| &p.ident)
	}

	/// Returns the generics for the `impl` block.
	fn impl_generics(&self) -> impl Iterator<Item = &TypeParam> {
		self.params.iter()
	}
}

impl Parse for SimpleGenerics {
	fn parse(input: ParseStream<'_>) -> Result<Self> {
		Ok(Self {
			lt_token: input.parse()?,
			params: Punctuated::parse_separated_nonempty(input)?,
			gt_token: input.parse()?,
		})
	}
}

impl ToTokens for SimpleGenerics {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.lt_token.to_tokens(tokens);
		self.params.to_tokens(tokens);
		self.gt_token.to_tokens(tokens);
	}
}

mod storage_types {
	syn::custom_keyword!(StorageValue);
	syn::custom_keyword!(StorageMap);
	syn::custom_keyword!(CountedStorageMap);
	syn::custom_keyword!(StorageDoubleMap);
	syn::custom_keyword!(StorageNMap);
}

/// The types of prefixes the storage alias macro supports.
mod prefix_types {
	// Use the verbatim/unmodified input name as the prefix.
	syn::custom_keyword!(verbatim);
	// The input type is a pallet and its pallet name should be used as the prefix.
	syn::custom_keyword!(pallet_name);
	// The input type implements `Get<'static str>` and this `str` should be used as the prefix.
	syn::custom_keyword!(dynamic);
}

/// The supported storage types
enum StorageType {
	Value {
		_kw: storage_types::StorageValue,
		_lt_token: Token![<],
		prefix: Type,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	Map {
		_kw: storage_types::StorageMap,
		_lt_token: Token![<],
		prefix: Type,
		_hasher_comma: Token![,],
		hasher_ty: Type,
		_key_comma: Token![,],
		key_ty: Type,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	CountedMap {
		_kw: storage_types::CountedStorageMap,
		_lt_token: Token![<],
		prefix: Type,
		_hasher_comma: Token![,],
		hasher_ty: Type,
		_key_comma: Token![,],
		key_ty: Type,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	DoubleMap {
		_kw: storage_types::StorageDoubleMap,
		_lt_token: Token![<],
		prefix: Type,
		_hasher1_comma: Token![,],
		hasher1_ty: Type,
		_key1_comma: Token![,],
		key1_ty: Type,
		_hasher2_comma: Token![,],
		hasher2_ty: Type,
		_key2_comma: Token![,],
		key2_ty: Type,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	NMap {
		_kw: storage_types::StorageNMap,
		_lt_token: Token![<],
		prefix: Type,
		_paren_comma: Token![,],
		_paren_token: token::Paren,
		key_types: Punctuated<Type, Token![,]>,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
}

impl StorageType {
	/// Generate the actual type declaration.
	fn generate_type_declaration(
		&self,
		crate_: &Ident,
		storage_instance: &StorageInstance,
		storage_name: &Ident,
		storage_generics: Option<&SimpleGenerics>,
		visibility: &Visibility,
		attributes: &[Attribute],
	) -> TokenStream {
		let storage_instance_generics = &storage_instance.generics;
		let storage_instance = &storage_instance.name;
		let attributes = attributes.iter();
		let storage_generics = storage_generics.map(|g| {
			let generics = g.type_generics();

			quote!( < #( #generics ),* > )
		});

		match self {
			Self::Value { value_ty, query_type, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageValue<
						#storage_instance #storage_instance_generics,
						#value_ty
						#query_type
					>;
				}
			},
			Self::CountedMap { value_ty, query_type, hasher_ty, key_ty, .. } |
			Self::Map { value_ty, query_type, hasher_ty, key_ty, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));
				let map_type = Ident::new(
					match self {
						Self::Map { .. } => "StorageMap",
						_ => "CountedStorageMap",
					},
					Span::call_site(),
				);

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::#map_type<
						#storage_instance #storage_instance_generics,
						#hasher_ty,
						#key_ty,
						#value_ty
						#query_type
					>;
				}
			},
			Self::DoubleMap {
				value_ty,
				query_type,
				hasher1_ty,
				key1_ty,
				hasher2_ty,
				key2_ty,
				..
			} => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageDoubleMap<
						#storage_instance #storage_instance_generics,
						#hasher1_ty,
						#key1_ty,
						#hasher2_ty,
						#key2_ty,
						#value_ty
						#query_type
					>;
				}
			},
			Self::NMap { value_ty, query_type, key_types, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));
				let key_types = key_types.iter();

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageNMap<
						#storage_instance #storage_instance_generics,
						( #( #key_types ),* ),
						#value_ty
						#query_type
					>;
				}
			},
		}
	}

	/// The prefix for this storage type.
	fn prefix(&self) -> &Type {
		match self {
			Self::Value { prefix, .. } |
			Self::Map { prefix, .. } |
			Self::CountedMap { prefix, .. } |
			Self::NMap { prefix, .. } |
			Self::DoubleMap { prefix, .. } => prefix,
		}
	}
}

impl Parse for StorageType {
	fn parse(input: ParseStream<'_>) -> Result<Self> {
		let lookahead = input.lookahead1();

		let parse_query_type = |input: ParseStream<'_>| -> Result<Option<(Token![,], Type)>> {
			if input.peek(Token![,]) && !input.peek2(Token![>]) {
				Ok(Some((input.parse()?, input.parse()?)))
			} else {
				Ok(None)
			}
		};

		if lookahead.peek(storage_types::StorageValue) {
			Ok(Self::Value {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				_value_comma: input.parse()?,
				value_ty: input.parse()?,
				query_type: parse_query_type(input)?,
				_trailing_comma: input.peek(Token![,]).then(|| input.parse()).transpose()?,
				_gt_token: input.parse()?,
			})
		} else if lookahead.peek(storage_types::StorageMap) {
			Ok(Self::Map {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				_hasher_comma: input.parse()?,
				hasher_ty: input.parse()?,
				_key_comma: input.parse()?,
				key_ty: input.parse()?,
				_value_comma: input.parse()?,
				value_ty: input.parse()?,
				query_type: parse_query_type(input)?,
				_trailing_comma: input.peek(Token![,]).then(|| input.parse()).transpose()?,
				_gt_token: input.parse()?,
			})
		} else if lookahead.peek(storage_types::CountedStorageMap) {
			Ok(Self::CountedMap {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				_hasher_comma: input.parse()?,
				hasher_ty: input.parse()?,
				_key_comma: input.parse()?,
				key_ty: input.parse()?,
				_value_comma: input.parse()?,
				value_ty: input.parse()?,
				query_type: parse_query_type(input)?,
				_trailing_comma: input.peek(Token![,]).then(|| input.parse()).transpose()?,
				_gt_token: input.parse()?,
			})
		} else if lookahead.peek(storage_types::StorageDoubleMap) {
			Ok(Self::DoubleMap {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				_hasher1_comma: input.parse()?,
				hasher1_ty: input.parse()?,
				_key1_comma: input.parse()?,
				key1_ty: input.parse()?,
				_hasher2_comma: input.parse()?,
				hasher2_ty: input.parse()?,
				_key2_comma: input.parse()?,
				key2_ty: input.parse()?,
				_value_comma: input.parse()?,
				value_ty: input.parse()?,
				query_type: parse_query_type(input)?,
				_trailing_comma: input.peek(Token![,]).then(|| input.parse()).transpose()?,
				_gt_token: input.parse()?,
			})
		} else if lookahead.peek(storage_types::StorageNMap) {
			let content;
			Ok(Self::NMap {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				_paren_comma: input.parse()?,
				_paren_token: parenthesized!(content in input),
				key_types: Punctuated::parse_terminated(&content)?,
				_value_comma: input.parse()?,
				value_ty: input.parse()?,
				query_type: parse_query_type(input)?,
				_trailing_comma: input.peek(Token![,]).then(|| input.parse()).transpose()?,
				_gt_token: input.parse()?,
			})
		} else {
			Err(lookahead.error())
		}
	}
}

/// The input expected by this macro.
struct Input {
	attributes: Vec<Attribute>,
	visibility: Visibility,
	_type: Token![type],
	storage_name: Ident,
	storage_generics: Option<SimpleGenerics>,
	where_clause: Option<WhereClause>,
	_equal: Token![=],
	storage_type: StorageType,
	_semicolon: Token![;],
}

impl Parse for Input {
	fn parse(input: ParseStream<'_>) -> Result<Self> {
		let attributes = input.call(Attribute::parse_outer)?;
		let visibility = input.parse()?;
		let _type = input.parse()?;
		let storage_name = input.parse()?;

		let lookahead = input.lookahead1();
		let storage_generics = if lookahead.peek(Token![<]) {
			Some(input.parse()?)
		} else if lookahead.peek(Token![=]) {
			None
		} else {
			return Err(lookahead.error())
		};

		let lookahead = input.lookahead1();
		let where_clause = if lookahead.peek(Token![where]) {
			Some(input.parse()?)
		} else if lookahead.peek(Token![=]) {
			None
		} else {
			return Err(lookahead.error())
		};

		let _equal = input.parse()?;

		let storage_type = input.parse()?;

		let _semicolon = input.parse()?;

		Ok(Self {
			attributes,
			visibility,
			_type,
			storage_name,
			storage_generics,
			_equal,
			storage_type,
			where_clause,
			_semicolon,
		})
	}
}

/// Defines which type of prefix the storage alias is using.
#[derive(Clone, Copy)]
enum PrefixType {
	/// An appropriate prefix will be determined automatically.
	///
	/// If generics are passed, this is assumed to be a pallet and the pallet name should be used.
	/// Otherwise use the verbatim passed name as prefix.
	Compatibility,
	/// The provided ident/name will be used as the prefix.
	Verbatim,
	/// The provided type will be used to determine the prefix. This type must
	/// implement `PalletInfoAccess` which specifies the proper name. This
	/// name is then used as the prefix.
	PalletName,
	/// Uses the provided type implementing `Get<'static str>` to determine the prefix.
	Dynamic,
}

/// Implementation of the `storage_alias` attribute macro.
pub fn storage_alias(attributes: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let input = syn::parse2::<Input>(input)?;
	let crate_ = generate_crate_access_2018("frame-support")?;

	let prefix_type = if attributes.is_empty() {
		PrefixType::Compatibility
	} else if syn::parse2::<prefix_types::verbatim>(attributes.clone()).is_ok() {
		PrefixType::Verbatim
	} else if syn::parse2::<prefix_types::pallet_name>(attributes.clone()).is_ok() {
		PrefixType::PalletName
	} else if syn::parse2::<prefix_types::dynamic>(attributes.clone()).is_ok() {
		PrefixType::Dynamic
	} else {
		return Err(Error::new(attributes.span(), "Unknown attributes"))
	};

	let storage_instance = generate_storage_instance(
		&crate_,
		&input.storage_name,
		input.storage_generics.as_ref(),
		input.where_clause.as_ref(),
		input.storage_type.prefix(),
		&input.visibility,
		matches!(input.storage_type, StorageType::CountedMap { .. }),
		prefix_type,
	)?;

	let definition = input.storage_type.generate_type_declaration(
		&crate_,
		&storage_instance,
		&input.storage_name,
		input.storage_generics.as_ref(),
		&input.visibility,
		&input.attributes,
	);

	let storage_instance_code = storage_instance.code;

	Ok(quote! {
		#storage_instance_code

		#definition
	})
}

/// The storage instance to use for the storage alias.
struct StorageInstance {
	name: Ident,
	generics: TokenStream,
	code: TokenStream,
}

/// Generate the [`StorageInstance`] for the storage alias.
fn generate_storage_instance(
	crate_: &Ident,
	storage_name: &Ident,
	storage_generics: Option<&SimpleGenerics>,
	storage_where_clause: Option<&WhereClause>,
	prefix: &Type,
	visibility: &Visibility,
	is_counted_map: bool,
	prefix_type: PrefixType,
) -> Result<StorageInstance> {
	if let Type::Infer(_) = prefix {
		return Err(Error::new(prefix.span(), "`_` is not allowed as prefix by `storage_alias`."))
	}

	let impl_generics_used_by_prefix = storage_generics
		.as_ref()
		.map(|g| {
			g.impl_generics()
				.filter(|g| prefix.contains_ident(&g.ident))
				.collect::<Vec<_>>()
		})
		.unwrap_or_default();

	let (pallet_prefix, impl_generics, type_generics) = match prefix_type {
		PrefixType::Compatibility =>
			if !impl_generics_used_by_prefix.is_empty() {
				let type_generics = impl_generics_used_by_prefix.iter().map(|g| &g.ident);
				let impl_generics = impl_generics_used_by_prefix.iter();

				(
					quote! {
						< #prefix as #crate_::traits::PalletInfoAccess>::name()
					},
					quote!( #( #impl_generics ),* ),
					quote!( #( #type_generics ),* ),
				)
			} else if let Some(prefix) = prefix.get_ident() {
				let prefix_str = prefix.to_string();

				(quote!(#prefix_str), quote!(), quote!())
			} else {
				return Err(Error::new_spanned(
					prefix,
					"If there are no generics, the prefix is only allowed to be an identifier.",
				))
			},
		PrefixType::Verbatim => {
			let prefix_str = match prefix.get_ident() {
				Some(p) => p.to_string(),
				None =>
					return Err(Error::new_spanned(
						prefix,
						"Prefix type `verbatim` requires that the prefix is an ident.",
					)),
			};

			(quote!(#prefix_str), quote!(), quote!())
		},
		PrefixType::PalletName => {
			let type_generics = impl_generics_used_by_prefix.iter().map(|g| &g.ident);
			let impl_generics = impl_generics_used_by_prefix.iter();

			(
				quote! {
					<#prefix as #crate_::traits::PalletInfoAccess>::name()
				},
				quote!( #( #impl_generics ),* ),
				quote!( #( #type_generics ),* ),
			)
		},
		PrefixType::Dynamic => {
			let type_generics = impl_generics_used_by_prefix.iter().map(|g| &g.ident);
			let impl_generics = impl_generics_used_by_prefix.iter();

			(
				quote! {
					<#prefix as #crate_::traits::Get<_>>::get()
				},
				quote!( #( #impl_generics ),* ),
				quote!( #( #type_generics ),* ),
			)
		},
	};

	let where_clause = storage_where_clause.map(|w| quote!(#w)).unwrap_or_default();

	let name_str = format!("{}_Storage_Instance", storage_name);
	let name = Ident::new(&name_str, Span::call_site());
	let storage_name_str = storage_name.to_string();

	let counter_code = is_counted_map.then(|| {
		let counter_name = Ident::new(&counter_prefix(&name_str), Span::call_site());
		let counter_storage_name_str = counter_prefix(&storage_name_str);

		quote! {
			#visibility struct #counter_name< #impl_generics >(
				#crate_::__private::sp_std::marker::PhantomData<(#type_generics)>
			) #where_clause;

			impl<#impl_generics> #crate_::traits::StorageInstance
				for #counter_name< #type_generics > #where_clause
			{
				fn pallet_prefix() -> &'static str {
					#pallet_prefix
				}

				const STORAGE_PREFIX: &'static str = #counter_storage_name_str;
			}

			impl<#impl_generics> #crate_::storage::types::CountedStorageMapInstance
				for #name< #type_generics > #where_clause
			{
				type CounterPrefix = #counter_name < #type_generics >;
			}
		}
	});

	// Implement `StorageInstance` trait.
	let code = quote! {
		#[allow(non_camel_case_types)]
		#visibility struct #name< #impl_generics >(
			#crate_::__private::sp_std::marker::PhantomData<(#type_generics)>
		) #where_clause;

		impl<#impl_generics> #crate_::traits::StorageInstance
			for #name< #type_generics > #where_clause
		{
			fn pallet_prefix() -> &'static str {
				#pallet_prefix
			}

			const STORAGE_PREFIX: &'static str = #storage_name_str;
		}

		#counter_code
	};

	Ok(StorageInstance { name, code, generics: quote!( < #type_generics > ) })
}
