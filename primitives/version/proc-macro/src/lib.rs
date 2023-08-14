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

//! A proc-macro that generates a custom wasm section from a given RuntimeVersion declaration
//!
//! This macro is re-exported from the `sp_version::runtime_version` and intended to be used from
//! there. Documentation can also be found there.

#![recursion_limit = "512"]

use proc_macro::TokenStream;

mod decl_runtime_version;

#[proc_macro_attribute]
pub fn runtime_version(_: TokenStream, input: TokenStream) -> TokenStream {
	decl_runtime_version::decl_runtime_version_impl(input)
}
