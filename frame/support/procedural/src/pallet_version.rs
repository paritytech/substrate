// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Implementation of macros related to pallet versioning.

use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Span, TokenStream};
use std::{env, str::FromStr};
use syn::{Error, Result};

/// Get the version from the given version environment variable.
///
/// The version is parsed into the requested destination type.
fn get_version<T: FromStr>(version_env: &str) -> std::result::Result<T, ()> {
	let version = env::var(version_env)
		.unwrap_or_else(|_| panic!("`{}` is always set by cargo; qed", version_env));

	T::from_str(&version).map_err(drop)
}

/// Create an error that will be shown by rustc at the call site of the macro.
fn create_error(message: &str) -> Error {
	Error::new(Span::call_site(), message)
}

/// Implementation of the `crate_to_pallet_version!` macro.
pub fn crate_to_pallet_version(input: proc_macro::TokenStream) -> Result<TokenStream> {
	if !input.is_empty() {
		return Err(create_error("No arguments expected!"))
	}

	let major_version = get_version::<u16>("CARGO_PKG_VERSION_MAJOR")
		.map_err(|_| create_error("Major version needs to fit into `u16`"))?;

	let minor_version = get_version::<u8>("CARGO_PKG_VERSION_MINOR")
		.map_err(|_| create_error("Minor version needs to fit into `u8`"))?;

	let patch_version = get_version::<u8>("CARGO_PKG_VERSION_PATCH")
		.map_err(|_| create_error("Patch version needs to fit into `u8`"))?;

	let crate_ = generate_crate_access_2018("frame-support")?;

	Ok(quote::quote! {
		#crate_::traits::PalletVersion {
			major: #major_version,
			minor: #minor_version,
			patch: #patch_version,
		}
	})
}
