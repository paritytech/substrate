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

use proc_macro2::{TokenStream, Span};
use syn::{Result, Error};
use std::{convert::TryInto, env, fmt::Display, path::PathBuf};
use frame_support_procedural_tools::generate_crate_access_2018;
use cargo_metadata::MetadataCommand;

/// Create an error that will be shown by rustc at the call site of the macro.
fn create_error(message: impl Display) -> Error {
	Error::new(Span::call_site(), message)
}

/// Implementation of the `pallet_version!` macro.
pub fn pallet_version(input: proc_macro::TokenStream) -> Result<TokenStream> {
	if !input.is_empty() {
		return Err(create_error("No arguments expected!"))
	}

	let cargo_toml = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR").expect("`CARGO_MANIFEST_DIR` is set by cargo"),
	).join("Cargo.toml");

	let metadata = MetadataCommand::new()
		.manifest_path(cargo_toml)
		.exec()
		.expect("`cargo metadata` can not fail on project `Cargo.toml`; qed");

	let package = metadata.root_package().expect("We specified a manifest path; qed");

	let version: u16 = if let Some(frame) = package.metadata.get("frame").and_then(|f| f.as_object()) {
		if let Some(key) = frame.keys().find(|k| *k != "pallet-version") {
			return Err(create_error(format!("Unknown key in package.metadata.frame: {}", key)))
		}

		if let Some(pallet_version) = frame.get("pallet-version") {
			if let Some(pallet_version) = pallet_version.as_u64() {
				pallet_version
					.try_into()
					.map_err(|_|
						create_error(
							"package.metadata.frame.pallet-version supports in maximum u16."
						)
					)?
			} else {
				return Err(
					create_error("package.metadata.frame.pallet-version is required to be a number"),
				)
			}
		} else {
			1
		}
	} else {
		1
	};

	let crate_ = generate_crate_access_2018("frame-support")?;

	Ok(quote::quote! { #crate_::traits::PalletVersion::new(#version) })
}
