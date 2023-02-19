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

//! Implementation of macros related to crate versioning.

use super::get_cargo_env_var;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Span, TokenStream};
use syn::{Error, Result};

/// Create an error that will be shown by rustc at the call site of the macro.
fn create_error(message: &str) -> Error {
	Error::new(Span::call_site(), message)
}

/// Implementation of the `crate_to_crate_version!` macro.
pub fn crate_to_crate_version(input: proc_macro::TokenStream) -> Result<TokenStream> {
	if !input.is_empty() {
		return Err(create_error("No arguments expected!"))
	}

	let major_version = get_cargo_env_var::<u16>("CARGO_PKG_VERSION_MAJOR")
		.map_err(|_| create_error("Major version needs to fit into `u16`"))?;

	let minor_version = get_cargo_env_var::<u8>("CARGO_PKG_VERSION_MINOR")
		.map_err(|_| create_error("Minor version needs to fit into `u8`"))?;

	let patch_version = get_cargo_env_var::<u8>("CARGO_PKG_VERSION_PATCH")
		.map_err(|_| create_error("Patch version needs to fit into `u8`"))?;

	let crate_ = generate_crate_access_2018("frame-support")?;

	Ok(quote::quote! {
		#crate_::traits::CrateVersion {
			major: #major_version,
			minor: #minor_version,
			patch: #patch_version,
		}
	})
}
