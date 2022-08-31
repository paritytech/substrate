// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Macros for declaring and implementing runtime apis.

#![recursion_limit = "512"]

use proc_macro::TokenStream;

mod impl_runtime_apis;
mod mock_impl_runtime_apis;
mod decl_runtime_apis;
mod utils;

#[proc_macro]
pub fn impl_runtime_apis(input: TokenStream) -> TokenStream {
	impl_runtime_apis::impl_runtime_apis_impl(input)
}

#[proc_macro]
pub fn mock_impl_runtime_apis(input: TokenStream) -> TokenStream {
	mock_impl_runtime_apis::mock_impl_runtime_apis_impl(input)
}

#[proc_macro]
pub fn decl_runtime_apis(input: TokenStream) -> TokenStream {
	decl_runtime_apis::decl_runtime_apis_impl(input)
}
