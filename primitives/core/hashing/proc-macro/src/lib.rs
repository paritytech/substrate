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

//! Macros to calculate constant hash bytes result.
//!
//! Macros from this crate does apply a specific hash function on input.
//! Input can be literal byte array as `b"content"` or array of bytes
//! as `[1, 2, 3]`.
//! Rust indent can also be use, in this case we use their utf8 string
//! byte representation, for instance if the ident is `MyStruct`, then
//! `b"MyStruct"` will be hash.
//! If multiple arguments comma separated are passed, they are concatenated
//! then hashed.
//!
//! ```rust
//! assert_eq!(
//! 	sp_core_hashing_proc_macro::blake2b_256!(b"test"),
//! 	&sp_core_hashing::blake2_256(b"test"),
//! );
//! let _ = sp_core_hashing_proc_macro::blake2b_256!([1u8]);
//! let _ = sp_core_hashing_proc_macro::blake2b_256!([1, 2, 3]);
//! ```

mod impls;

use impls::MultipleInputBytes;
use proc_macro::TokenStream;

/// Process a Blake2 64-bit hash of bytes parameter, outputs a `&'static [u8; 8]`..
#[proc_macro]
pub fn blake2b_64(input: TokenStream) -> TokenStream {
	impls::blake2b_64(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

/// Apply a Blake2 256-bit hash of bytes parameter, outputs a `&'static [u8; 32]`.
#[proc_macro]
pub fn blake2b_256(input: TokenStream) -> TokenStream {
	impls::blake2b_256(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

/// Apply a Blake2 512-bit hash of bytes parameter, outputs a `&'static [u8; 64]`.
#[proc_macro]
pub fn blake2b_512(input: TokenStream) -> TokenStream {
	impls::blake2b_512(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

/// Apply a XX 64-bit hash on its bytes parameter, outputs a `&'static [u8; 8]`.
#[proc_macro]
pub fn twox_64(input: TokenStream) -> TokenStream {
	impls::twox_64(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}

/// Apply a XX 128-bit hash on its bytes parameter, outputsa a `&'static [u8; 16]`.
#[proc_macro]
pub fn twox_128(input: TokenStream) -> TokenStream {
	impls::twox_128(syn::parse_macro_input!(input as MultipleInputBytes).concatenated())
}
