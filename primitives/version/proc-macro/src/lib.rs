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

//! An attribute that accepts a version declaration of a runtime and generates a custom wasm section
//! with the equivalent contents.
//!
//! The custom section allows to read the version of the runtime without having to execute any code.
//! Instead, the generated custom section can be relatively easily parsed from the wasm binary. The
//! identifier of the custom section is "runtime_version".
//!
//! A shortcoming of this macro is that it is unable to embed information regarding supported APIs.
//! This is supported by the `construct_runtime!` macro.
//!
//! This macro accepts a const item like the following:
//!
//! ```rust,ignore
//! #[sp_version_proc_macro::runtime_version]
//! pub const VERSION: RuntimeVersion = RuntimeVersion {
//! 	spec_name: create_runtime_str!("test"),
//! 	impl_name: create_runtime_str!("test"),
//! 	authoring_version: 10,
//! 	spec_version: 265,
//! 	impl_version: 1,
//! 	apis: RUNTIME_API_VERSIONS,
//! 	transaction_version: 2,
//! };
//! ```
//!
//! It will pass it through and add code required for emitting a custom section. The information that
//! will go into the custom section is parsed from the item declaration. Due to that, the macro is
//! somewhat rigid in terms of the code it accepts. There are the following considerations:
//!
//! - The `spec_name` and `impl_name` must be set by a macro-like expression. The name of the macro
//!   doesn't matter though.
//!
//! - `authoring_version`, `spec_version`, `impl_version` and `transaction_version` must be set
//!   by a literal. Literal must be an integer. No other expressions are allowed there. In particular,
//!   you can't supply a constant variable.
//!
//! - `apis` doesn't have any specific constraints. This is because this information doesn't get into
//!   the custom section and is not parsed.
//!

#![recursion_limit = "512"]

use proc_macro::TokenStream;

mod decl_runtime_version;

#[proc_macro_attribute]
pub fn runtime_version(_: TokenStream, input: TokenStream) -> TokenStream {
	decl_runtime_version::decl_runtime_version_impl(input)
}
