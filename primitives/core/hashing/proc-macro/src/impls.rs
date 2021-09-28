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

use syn::parse::{Parse, ParseStream};

use proc_macro::{Literal, TokenStream, TokenTree};

pub(super) struct InputBytes(pub Vec<u8>);

pub(super) struct MultipleInputBytes(pub Vec<Vec<u8>>);

impl MultipleInputBytes {
	pub(super) fn concatenated(mut self) -> Vec<u8> {
		if self.0.len() == 0 {
			Vec::new()
		} else {
			let mut result = core::mem::take(&mut self.0[0]);
			for other in self.0[1..].iter_mut() {
				result.append(other);
			}
			result
		}
	}
}

impl Parse for InputBytes {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		match <syn::ExprArray>::parse(input) {
			Ok(array) => {
				let mut bytes = Vec::<u8>::new();
				for expr in array.elems.iter() {
					match expr {
						syn::Expr::Lit(lit) => match &lit.lit {
							syn::Lit::Int(b) => {
								let v: u8 = b.base10_parse()?;
								bytes.push(v)
							},
							syn::Lit::Byte(b) => bytes.push(b.value()),
							_ =>
								return Err(syn::Error::new(
									input.span(),
									"Expected array of u8 elements.".to_string(),
								)),
						},
						_ =>
							return Err(syn::Error::new(
								input.span(),
								"Expected array of u8 elements.".to_string(),
							)),
					}
				}
				return Ok(InputBytes(bytes))
			},
			Err(_e) => (),
		}
		// use rust names as a vec of their utf8 bytecode.
		match <syn::Ident>::parse(input) {
			Ok(ident) => return Ok(InputBytes(ident.to_string().as_bytes().to_vec())),
			Err(_e) => (),
		}
		Ok(InputBytes(<syn::LitByteStr>::parse(input)?.value()))
	}
}

impl Parse for MultipleInputBytes {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let elts =
			syn::punctuated::Punctuated::<InputBytes, syn::token::Comma>::parse_terminated(input)?;
		Ok(MultipleInputBytes(elts.into_iter().map(|elt| elt.0).collect()))
	}
}

pub(super) fn twox_64(bytes: Vec<u8>) -> TokenStream {
	let result = sp_core_hashing::twox_64(bytes.as_slice());
	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}

pub(super) fn twox_128(bytes: Vec<u8>) -> TokenStream {
	let result = sp_core_hashing::twox_128(bytes.as_slice());
	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}

pub(super) fn blake2b_512(bytes: Vec<u8>) -> TokenStream {
	let result = sp_core_hashing::blake2_512(bytes.as_slice());
	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}

pub(super) fn blake2b_256(bytes: Vec<u8>) -> TokenStream {
	let result = sp_core_hashing::blake2_256(bytes.as_slice());
	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}

pub(super) fn blake2b_64(bytes: Vec<u8>) -> TokenStream {
	let result = sp_core_hashing::blake2_64(bytes.as_slice());
	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}
