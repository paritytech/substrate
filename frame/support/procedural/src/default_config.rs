// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, ItemImpl, Path, PathArguments, PathSegment, Result, Token, parse::Parser, punctuated::Punctuated, spanned::Spanned};

pub fn use_default_config_for(attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
	let config_impl: ItemImpl = syn::parse(input)?;
	let config_impl_span = config_impl.span();
	let (_, config_trait, _) = config_impl.trait_.ok_or_else(|| {
		let msg = "impl block does not implement a pallet Config trait";
		syn::Error::new(config_impl_span, msg)
	})?;
	let ItemImpl { attrs, generics, self_ty, items, .. } = config_impl;
	let config_opts = Punctuated::<Ident, Token![,]>::parse_terminated.parse(attr)?;
	let default_items = config_opts.iter().map(|config_item_ident| {
		let path = construct_path_to_macro(&config_trait);
		quote!(#path::use_default_config_for!(#config_item_ident);)
	})
	.collect::<Vec<_>>();

	Ok(quote! {
		#(#attrs)*
		impl<#generics> #config_trait for #self_ty {
			#(#items)*
			#(#default_items)*
		}
	}.into())
}

fn construct_path_to_macro(config_trait: &Path) -> Path {
	let mut path = config_trait.clone();
	path.segments.pop();
	path.segments.push(PathSegment {
		ident: format_ident!("__substrate_config_defaults"),
		arguments: PathArguments::None,
	});
	path
}
