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

mod keyword {
	syn::custom_keyword!(HoldReason);
}

pub struct HoldReasonDef {
	/// The index of the HoldReason item in the pallet module.
	pub index: usize,
	/// The HoldReason keyword used (contains span).
	pub hold_reason: keyword::HoldReason,
	/// The span of the pallet::hold_reason attribute.
	pub attr_span: proc_macro2::Span,
}

impl HoldReasonDef {
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
				"Invalid pallet::hold_reason, expected enum item",
			))
		};

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::hold_reason, `HoldReason` must be public";
			return Err(syn::Error::new(item.span(), msg))
		}

		let has_derive_attr = item
			.attrs
			.iter()
			.any(|attr| {
				attr.parse_meta()
					.ok()
					.map(|meta| match meta {
						syn::Meta::List(syn::MetaList { path, .. }) =>
							path.get_ident().map(|ident| ident == "derive").unwrap_or(false),
						_ => false,
					})
					.unwrap_or(false)
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

		let hold_reason = syn::parse2::<keyword::HoldReason>(item.ident.to_token_stream())?;

		Ok(HoldReasonDef { index, hold_reason, attr_span })
	}
}
