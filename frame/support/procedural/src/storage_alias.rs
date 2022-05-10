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

//! Implementation of the `storage_alias` attribute macro.

use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
	ext::IdentExt,
	parenthesized,
	parse::{Parse, ParseStream},
	punctuated::Punctuated,
	token, Attribute, Error, Ident, Result, Token, Type, TypeParam, Visibility,
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

	/// Returns `true` if all parameters have at least one trait bound.
	fn all_have_trait_bounds(&self) -> bool {
		self.params
			.iter()
			.all(|p| p.bounds.iter().any(|b| matches!(b, syn::TypeParamBound::Trait(_))))
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
	syn::custom_keyword!(Value);
	syn::custom_keyword!(Map);
	syn::custom_keyword!(DoubleMap);
	syn::custom_keyword!(NMap);
}

/// The supported storage types
enum StorageType {
	Value {
		_kw: storage_types::Value,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<SimpleGenerics>,
		_value_comma: Token![,],
		value_ty: Type,
		query_type: Option<(Token![,], Type)>,
		_trailing_comma: Option<Token![,]>,
		_gt_token: Token![>],
	},
	Map {
		_kw: storage_types::Map,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<SimpleGenerics>,
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
		_kw: storage_types::DoubleMap,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<SimpleGenerics>,
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
		_kw: storage_types::NMap,
		_lt_token: Token![<],
		prefix: SimplePath,
		prefix_generics: Option<SimpleGenerics>,
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
		let type_generics = self
			.prefix_generics()
			.map(|g| {
				let g = g.type_generics();
				quote! { <#( #g ),*> }
			})
			.unwrap_or_default();
		let attributes = attributes.iter();

		match self {
			Self::Value { value_ty, query_type, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageValue<
						#storage_instance #type_generics,
						#value_ty
						#query_type
					>;
				}
			},
			Self::Map { value_ty, query_type, hasher_ty, key_ty, .. } => {
				let query_type = query_type.as_ref().map(|(c, t)| quote!(#c #t));

				quote! {
					#( #attributes )*
					#visibility type #storage_name #storage_generics = #crate_::storage::types::StorageMap<
						#storage_instance #type_generics,
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
						#storage_instance #type_generics,
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
						#storage_instance #type_generics,
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
			Self::NMap { prefix, .. } |
			Self::DoubleMap { prefix, .. } => prefix,
		}
	}

	/// The prefix generics for this storage type.
	fn prefix_generics(&self) -> Option<&SimpleGenerics> {
		match self {
			Self::Value { prefix_generics, .. } |
			Self::Map { prefix_generics, .. } |
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

		let parse_pallet_generics = |input: ParseStream<'_>| -> Result<Option<SimpleGenerics>> {
			let lookahead = input.lookahead1();
			if lookahead.peek(Token![<]) {
				let generics = input.parse::<SimpleGenerics>()?;

				if generics.all_have_trait_bounds() {
					Ok(Some(generics))
				} else {
					Err(Error::new_spanned(
						generics,
						"The pallet generics require to be bound by the \
						pallet `Config` trait and optional `Instance` trait.",
					))
				}
			} else if lookahead.peek(Token![,]) {
				Ok(None)
			} else {
				Err(lookahead.error())
			}
		};

		if lookahead.peek(storage_types::Value) {
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
		} else if lookahead.peek(storage_types::Map) {
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
		} else if lookahead.peek(storage_types::DoubleMap) {
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
		} else if lookahead.peek(storage_types::NMap) {
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
		let (storage_generics, _equal) = if lookahead.peek(Token![<]) {
			(Some(input.parse()?), input.parse()?)
		} else if lookahead.peek(Token![=]) {
			(None, input.parse()?)
		} else {
			return Err(lookahead.error())
		};

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
		input.storage_type.prefix(),
		input.storage_type.prefix_generics(),
		&input.visibility,
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
	prefix: &SimplePath,
	prefix_generics: Option<&SimpleGenerics>,
	visibility: &Visibility,
) -> Result<StorageInstance> {
	let (pallet_prefix, impl_generics, type_generics) =
		if let Some(prefix_generics) = prefix_generics {
			let type_generics = prefix_generics.type_generics();
			let type_generics2 = prefix_generics.type_generics();
			let impl_generics = prefix_generics.impl_generics();

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

	let name = Ident::new(&format!("{}_Storage_Instance", storage_name), Span::call_site());
	let storage_name_str = storage_name.to_string();

	// Implement `StorageInstance` trait.
	let code = quote! {
		#visibility struct #name< #impl_generics >(#crate_::sp_std::marker::PhantomData<(#type_generics)>);

		impl<#impl_generics> #crate_::traits::StorageInstance for #name< #type_generics > {
			fn pallet_prefix() -> &'static str {
				#pallet_prefix
			}

			const STORAGE_PREFIX: &'static str = #storage_name_str;
		}
	};

	Ok(StorageInstance { name, code })
}
