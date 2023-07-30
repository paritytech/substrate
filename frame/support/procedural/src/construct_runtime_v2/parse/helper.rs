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

use crate::pallet::parse::helper::MutItemAttrs;
use quote::ToTokens;

pub(crate) fn take_first_item_runtime_attr<Attr>(
	item: &mut impl MutItemAttrs,
) -> syn::Result<Option<Attr>>
where
	Attr: syn::parse::Parse,
{
	let attrs = if let Some(attrs) = item.mut_item_attrs() { attrs } else { return Ok(None) };

	if let Some(index) = attrs.iter().position(|attr| {
		attr.path().segments.first().map_or(false, |segment| segment.ident == "frame")
	}) {
		let runtime_attr = attrs.remove(index);
		Ok(Some(syn::parse2(runtime_attr.into_token_stream())?))
	} else {
		Ok(None)
	}
}
