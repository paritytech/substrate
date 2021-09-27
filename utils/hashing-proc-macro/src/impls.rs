// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

use proc_macro::{TokenStream, TokenTree, Literal};

pub(super) fn blake2b(size: usize, bytes: Vec<u8>) -> TokenStream {
	let result = blake2_rfc::blake2b::blake2b(size, &[], bytes.as_slice()).as_bytes().to_vec();
	TokenTree::Literal(Literal::byte_string(result.as_slice())).into()
}

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
						syn::Expr::Lit(lit) => {
							match &lit.lit {
								syn::Lit::Int(b) => {
									let v: u8 = b.base10_parse()?;
									bytes.push(v)
								},
								syn::Lit::Byte(b) => bytes.push(b.value()),
								_ => return Err(syn::Error::new(
									input.span(),
									"Expected array of u8 elements.".to_string(),
								)),
							}
						},
						_ => return Err(syn::Error::new(
							input.span(),
							"Expected array of u8 elements.".to_string(),
						)),
					}
				}
				return Ok(InputBytes(bytes))
			},
			Err(_e) => (),
		}
		Ok(InputBytes(<syn::LitByteStr>::parse(input)?.value()))
	}
}

impl Parse for MultipleInputBytes {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let elts = syn::punctuated::Punctuated::<InputBytes, syn::token::Comma>::parse_terminated(input)?;
		Ok(MultipleInputBytes(elts.into_iter().map(|elt| elt.0).collect()))
	}
}

pub(super) fn twox_64(bytes: Vec<u8>) -> TokenStream {
	use core::hash::Hasher;
	let mut h0 = twox_hash::XxHash::with_seed(0);
	h0.write(bytes.as_slice());
	let r0 = h0.finish();

	TokenTree::Literal(Literal::byte_string(&r0.to_le_bytes()[..])).into()
}

pub(super) fn twox_128(bytes: Vec<u8>) -> TokenStream {
	use core::hash::Hasher;
	let mut h0 = twox_hash::XxHash::with_seed(0);
	let mut h1 = twox_hash::XxHash::with_seed(1);
	h0.write(bytes.as_slice());
	h1.write(bytes.as_slice());
	let r0 = h0.finish();
	let r1 = h1.finish();
	let mut result = [0u8; 16];
	result[0..8].copy_from_slice(&r0.to_le_bytes()[..]);
	result[8..16].copy_from_slice(&r1.to_le_bytes()[..]);

	TokenTree::Literal(Literal::byte_string(&result[..])).into()
}
