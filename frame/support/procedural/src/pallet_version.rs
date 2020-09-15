// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

/// Implementation of the `crate_to_pallet_version!` macro.
pub fn crate_to_pallet_version(input: proc_macro::TokenStream) -> Result<TokenStream> {
	if !input.is_empty() {
		return Err(Error::new(Span::call_site(), "No arguments expected!"));
	}

	Ok(TokenStream::default())
}
