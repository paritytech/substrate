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

//! Macros to calculate constant hash bytes result.
//!
//! ```rust
//! assert_eq!(
//!		hashing_proc_macro::blake2b_32!(b"test"),
//!		blake2_rfc::blake2b::blake2b(32, &[], b"test").as_bytes(),
//!	);
//!	// let _ = hashing_proc_macro::blake2b_32!([b"test"]);
//!	let _ = hashing_proc_macro::blake2b_32!([1u8]);
//!	let _ = hashing_proc_macro::blake2b_32!([1, 2, 3]);
//! ```

mod impls;

use proc_macro::TokenStream;
use impls::MultipleInputBytes;

#[proc_macro]
pub fn blake2b_32(input: TokenStream) -> TokenStream {
	impls::blake2b(32, syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

#[proc_macro]
pub fn blake2b_64(input: TokenStream) -> TokenStream {
	impls::blake2b(64, syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

#[proc_macro]
pub fn twox_64(input: TokenStream) -> TokenStream {
	impls::twox_64(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

#[proc_macro]
pub fn twox_128(input: TokenStream) -> TokenStream {
	impls::twox_128(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}
