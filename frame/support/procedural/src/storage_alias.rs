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
	ext::IdentExt,
	parenthesized,
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	token, Attribute, Error, Ident, Result, Token, Type, TypeParam, Visibility, WhereClause,
};

/// Represents a path that only consists of [`Ident`] separated by `::`.
struct SimplePath {
	leading_colon: Option<Token![::]>,
	segments: Punctuated<Ident, Token![::]>,
}

impl SimplePath {
	/// Returns the [`Ident`] of this path.
	///
	/// It only returns `Some(_)` if there is exactly one element and no leading colon.
	fn get_ident(&self) -> Option<&Ident> {
		if self.segments.len() != 1 || self.leading_colon.is_some() {
			None
		} else {
			self.segments.first()
		}
	}
}

impl Parse for SimplePath {
	fn parse(input: ParseStream<'_>) -> Result<Self> {
		Ok(Self {
			leading_colon: if input.peek(Token![::]) { Some(input.parse()?) } else { None },
			segments: Punctuated::parse_separated_nonempty_with(input, |p| Ident::parse_any(p))?,
		})
	}
}

impl ToTokens for SimplePath {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.leading_colon.to_tokens(tokens);
		self.segments.to_tokens(tokens);
	}
}

/// Represents generics which only support [`Ident`] separated by commas as you would pass it to a
/// type.
struct TypeGenerics {
	lt_token: Token![<],
	params: Punctuated<Ident, token::Comma>,
	gt_token: Token![>],
}

impl TypeGenerics {
	/// Returns the generics for types declarations etc.
	fn iter(&self) -> impl Iterator<Item = &Ident> {
		self.params.iter()
	}
}

impl Parse for TypeGenerics {
	fn parse(input: ParseStream<'_>) -> Result<Self> {
		Ok(Self {
			lt_token: input.parse()?,
			params: Punctuated::parse_separated_nonempty(input)?,
			gt_token: input.parse()?,
		})
	}
}

impl ToTokens for TypeGenerics {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.lt_token.to_tokens(tokens);
		self.params.to_tokens(tokens);
		self.gt_token.to_tokens(tokens);
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

/// The supported storage types
enum StorageType {
	Value {
		_kw: storage_types::StorageValue,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<TypeGenerics>,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	Map {
		_kw: storage_types::StorageMap,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<TypeGenerics>,
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
		prefix: SimplePath,
		prefix_generics: Option<TypeGenerics>,
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
		prefix: SimplePath,
		prefix_generics: Option<TypeGenerics>,
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
		prefix: SimplePath,
		prefix_generics: Option<TypeGenerics>,
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
		let storage_instance = &storage_instance.name;
		let attributes = attributes.iter();
		let storage_generics = storage_generics.map(|g| {
			let generics = g.type_generics();

			quote!( < #( #generics ),* > )
		});

		match self {
			Self::Value { value_ty, query_type, prefix_generics, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageValue<
						#storage_instance #prefix_generics,
						#value_ty
						#query_type
					>;
				}
			},
			Self::CountedMap {
				value_ty, query_type, hasher_ty, key_ty, prefix_generics, ..
			} |
			Self::Map { value_ty, query_type, hasher_ty, key_ty, prefix_generics, .. } => {
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
						#storage_instance #prefix_generics,
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
				prefix_generics,
				..
			} => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageDoubleMap<
						#storage_instance #prefix_generics,
						#hasher1_ty,
						#key1_ty,
						#hasher2_ty,
						#key2_ty,
						#value_ty
						#query_type
					>;
				}
			},
			Self::NMap { value_ty, query_type, key_types, prefix_generics, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));
				let key_types = key_types.iter();

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageNMap<
						#storage_instance #prefix_generics,
						( #( #key_types ),* ),
						#value_ty
						#query_type
					>;
				}
			},
		}
	}

	/// The prefix for this storage type.
	fn prefix(&self) -> &SimplePath {
		match self {
			Self::Value { prefix, .. } |
			Self::Map { prefix, .. } |
			Self::CountedMap { prefix, .. } |
			Self::NMap { prefix, .. } |
			Self::DoubleMap { prefix, .. } => prefix,
		}
	}

	/// The prefix generics for this storage type.
	fn prefix_generics(&self) -> Option<&TypeGenerics> {
		match self {
			Self::Value { prefix_generics, .. } |
			Self::Map { prefix_generics, .. } |
			Self::CountedMap { prefix_generics, .. } |
			Self::NMap { prefix_generics, .. } |
			Self::DoubleMap { prefix_generics, .. } => prefix_generics.as_ref(),
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

		let parse_pallet_generics = |input: ParseStream<'_>| -> Result<Option<TypeGenerics>> {
			let lookahead = input.lookahead1();
			if lookahead.peek(Token![<]) {
				Ok(Some(input.parse()?))
			} else if lookahead.peek(Token![,]) {
				Ok(None)
			} else {
				Err(lookahead.error())
			}
		};

		if lookahead.peek(storage_types::StorageValue) {
			Ok(Self::Value {
				_kw: input.parse()?,
				_lt_token: input.parse()?,
				prefix: input.parse()?,
				prefix_generics: parse_pallet_generics(input)?,
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
				prefix_generics: parse_pallet_generics(input)?,
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
				prefix_generics: parse_pallet_generics(input)?,
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
				prefix_generics: parse_pallet_generics(input)?,
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
				prefix_generics: parse_pallet_generics(input)?,
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

/// Implementation of the `storage_alias` attribute macro.
pub fn storage_alias(input: TokenStream) -> Result<TokenStream> {
	let input = syn::parse2::<Input>(input)?;
	let crate_ = generate_crate_access_2018("frame-support")?;

	let storage_instance = generate_storage_instance(
		&crate_,
		&input.storage_name,
		input.storage_generics.as_ref(),
		input.where_clause.as_ref(),
		input.storage_type.prefix(),
		input.storage_type.prefix_generics(),
		&input.visibility,
		matches!(input.storage_type, StorageType::CountedMap { .. }),
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
	code: TokenStream,
}

/// Generate the [`StorageInstance`] for the storage alias.
fn generate_storage_instance(
	crate_: &Ident,
	storage_name: &Ident,
	storage_generics: Option<&SimpleGenerics>,
	storage_where_clause: Option<&WhereClause>,
	prefix: &SimplePath,
	prefix_generics: Option<&TypeGenerics>,
	visibility: &Visibility,
	is_counted_map: bool,
) -> Result<StorageInstance> {
	if let Some(ident) = prefix.get_ident().filter(|i| *i == "_") {
		return Err(Error::new(ident.span(), "`_` is not allowed as prefix by `storage_alias`."))
	}

	let (pallet_prefix, impl_generics, type_generics) =
		if let Some((prefix_generics, storage_generics)) =
			prefix_generics.and_then(|p| storage_generics.map(|s| (p, s)))
		{
			let type_generics = prefix_generics.iter();
			let type_generics2 = prefix_generics.iter();
			let impl_generics = storage_generics
				.impl_generics()
				.filter(|g| prefix_generics.params.iter().any(|pg| *pg == g.ident));

			(
				quote! {
					<#prefix < #( #type_generics2 ),* > as #crate_::traits::PalletInfoAccess>::name()
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
				#crate_::sp_std::marker::PhantomData<(#type_generics)>
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
		#visibility struct #name< #impl_generics >(
			#crate_::sp_std::marker::PhantomData<(#type_generics)>
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

	Ok(StorageInstance { name, code })
}
