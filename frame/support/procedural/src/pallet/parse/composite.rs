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

use quote::ToTokens;
use syn::spanned::Spanned;

pub mod keyword {
	use super::*;

	syn::custom_keyword!(FreezeReason);
	syn::custom_keyword!(HoldReason);
	syn::custom_keyword!(LockId);
	syn::custom_keyword!(SlashReason);
	pub enum CompositeKeyword {
		FreezeReason(FreezeReason),
		HoldReason(HoldReason),
		LockId(LockId),
		SlashReason(SlashReason),
	}

	impl ToTokens for CompositeKeyword {
		fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
			use CompositeKeyword::*;
			match self {
				FreezeReason(inner) => inner.to_tokens(tokens),
				HoldReason(inner) => inner.to_tokens(tokens),
				LockId(inner) => inner.to_tokens(tokens),
				SlashReason(inner) => inner.to_tokens(tokens),
			}
		}
	}

	impl syn::parse::Parse for CompositeKeyword {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			let lookahead = input.lookahead1();
			if lookahead.peek(FreezeReason) {
				Ok(Self::FreezeReason(input.parse()?))
			} else if lookahead.peek(HoldReason) {
				Ok(Self::HoldReason(input.parse()?))
			} else if lookahead.peek(LockId) {
				Ok(Self::LockId(input.parse()?))
			} else if lookahead.peek(SlashReason) {
				Ok(Self::SlashReason(input.parse()?))
			} else {
				Err(lookahead.error())
			}
		}
	}

	impl std::fmt::Display for CompositeKeyword {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			use CompositeKeyword::*;
			write!(
				f,
				"{}",
				match self {
					FreezeReason(_) => "FreezeReason",
					HoldReason(_) => "HoldReason",
					LockId(_) => "LockId",
					SlashReason(_) => "SlashReason",
				}
			)
		}
	}
}

pub struct CompositeDef {
	/// The index of the HoldReason item in the pallet module.
	pub index: usize,
	/// The composite keyword used (contains span).
	pub composite_keyword: keyword::CompositeKeyword,
	/// The span of the pallet::composite_enum attribute.
	pub attr_span: proc_macro2::Span,
}

impl CompositeDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		scrate: &proc_macro2::Ident,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Enum(item) = item {
			item
		} else {
			return Err(syn::Error::new(
				item.span(),
				"Invalid pallet::composite_enum, expected enum item",
			))
		};

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = format!("Invalid pallet::composite_enum, `{}` must be public", item.ident);
			return Err(syn::Error::new(item.span(), msg))
		}

		let has_derive_attr = item.attrs.iter().any(|attr| {
			if let syn::Meta::List(syn::MetaList { path, .. }) = &attr.meta {
				path.get_ident().map(|ident| ident == "derive").unwrap_or(false)
			} else {
				false
			}
		});

		if !has_derive_attr {
			let derive_attr: syn::Attribute = syn::parse_quote! {
				#[derive(
					Copy, Clone, Eq, PartialEq, Ord, PartialOrd,
					#scrate::codec::Encode, #scrate::codec::Decode, #scrate::codec::MaxEncodedLen,
					#scrate::scale_info::TypeInfo,
					#scrate::RuntimeDebug,
				)]
			};
			item.attrs.push(derive_attr);
		}

		let composite_keyword =
			syn::parse2::<keyword::CompositeKeyword>(item.ident.to_token_stream())?;

		Ok(CompositeDef { index, composite_keyword, attr_span })
	}
}
