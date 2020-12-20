// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Use to derive parsing for parsing struct.
// end::description[]

#![recursion_limit = "128"]

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::parse_macro_input;
use quote::quote;

pub(crate) fn fields_idents(
	fields: impl Iterator<Item = syn::Field>,
) -> impl Iterator<Item = proc_macro2::TokenStream> {
	fields.enumerate().map(|(ix, field)| {
		field.ident.map(|i| quote!{#i}).unwrap_or_else(|| {
			let f_ix: syn::Ident = syn::Ident::new(&format!("f_{}", ix), Span::call_site());
			quote!( #f_ix )
		})
	})
}

pub(crate) fn fields_access(
	fields: impl Iterator<Item = syn::Field>,
) -> impl Iterator<Item = proc_macro2::TokenStream> {
	fields.enumerate().map(|(ix, field)| {
		field.ident.map(|i| quote!( #i )).unwrap_or_else(|| {
			let f_ix: syn::Index = syn::Index {
				index: ix as u32,
				span: Span::call_site(),
			};
			quote!( #f_ix )
		})
	})
}

/// self defined parsing struct.
/// not meant for any struct, just for fast
/// parse implementation.
#[proc_macro_derive(Parse)]
pub fn derive_parse(input: TokenStream) -> TokenStream {
	let item = parse_macro_input!(input as syn::Item);
	match item {
		syn::Item::Struct(input) => derive_parse_struct(input),
		_ => TokenStream::new(), // ignore
	}
}

fn derive_parse_struct(input: syn::ItemStruct) -> TokenStream {
	let syn::ItemStruct {
		ident,
		generics,
		fields,
		..
	} = input;
	let field_names = {
		let name = fields_idents(fields.iter().map(Clone::clone));
		quote!{
			#(
				#name,
			)*
		}
	};
	let field = fields_idents(fields.iter().map(Clone::clone));
	let tokens = quote! {
		impl #generics syn::parse::Parse for #ident #generics {
			fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<Self> {
				#(
					let #field = input.parse()?;
				)*
				Ok(Self {
					#field_names
				})
			}
		}
	};
	tokens.into()
}

/// self defined parsing struct or enum.
/// not meant for any struct/enum, just for fast
/// parse implementation.
/// For enum:
///   it only output fields (empty field act as a None).
#[proc_macro_derive(ToTokens)]
pub fn derive_totokens(input: TokenStream) -> TokenStream {
	let item = parse_macro_input!(input as syn::Item);
	match item {
		syn::Item::Enum(input) => derive_totokens_enum(input),
		syn::Item::Struct(input) => derive_totokens_struct(input),
		_ => TokenStream::new(), // ignore
	}
}

fn derive_totokens_struct(input: syn::ItemStruct) -> TokenStream {
 let syn::ItemStruct {
		ident,
		generics,
		fields,
		..
	} = input;

	let fields = fields_access(fields.iter().map(Clone::clone));
	let tokens = quote! {

		impl #generics quote::ToTokens for #ident #generics {
			fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
				#(
					self.#fields.to_tokens(tokens);
				)*
			}
		}

	};
	tokens.into()
}

fn derive_totokens_enum(input: syn::ItemEnum) -> TokenStream {
	let syn::ItemEnum {
		ident,
		generics,
		variants,
		..
	} = input;
	let variants = variants.iter().map(|v| {
		let v_ident = v.ident.clone();
		let fields_build = if v.fields.iter().count() > 0 {
			let fields_id = fields_idents(v.fields.iter().map(Clone::clone));
			quote!( (#(#fields_id), *) )
		} else {
			quote!()
		};
		let field = fields_idents(v.fields.iter().map(Clone::clone));
		quote! {
			#ident::#v_ident#fields_build => {
				#(
					#field.to_tokens(tokens);
				)*
			},
		}
	});
	let tokens = quote! {
		impl #generics quote::ToTokens for #ident #generics {
			fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
				match self {
					#(
						#variants
					)*
				}
			}
		}
	};

	tokens.into()
}
