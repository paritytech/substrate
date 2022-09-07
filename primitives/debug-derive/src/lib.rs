// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Macros to derive runtime debug implementation.
//!
//! This custom derive implements a `core::fmt::Debug` trait,
//! but in case the `std` feature is enabled the implementation
//! will actually print out the structure as regular `derive(Debug)`
//! would do. If `std` is disabled the implementation will be empty.
//!
//! This behaviour is useful to prevent bloating the runtime WASM
//! blob from unneeded code.
//!
//! ```rust
//! #[derive(sp_debug_derive::RuntimeDebug)]
//! struct MyStruct;
//!
//! assert_eq!(format!("{:?}", MyStruct), "MyStruct");
//! ```

mod impls;

use proc_macro::TokenStream;

#[proc_macro_derive(RuntimeDebug)]
pub fn debug_derive(input: TokenStream) -> TokenStream {
   impls::debug_derive(syn::parse_macro_input!(input))
}

