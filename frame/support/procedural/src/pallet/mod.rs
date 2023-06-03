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

//! Implementation for pallet attribute macro.
//!
//! General workflow:
//! 1 - parse all pallet attributes:
//!   This step remove all attributes `#[pallet::*]` from the ItemMod and build the `Def` struct
//!   which holds the ItemMod without `#[pallet::*]` and information given by those attributes
//! 2 - expand from the parsed information
//!   This step will modify the ItemMod by adding some derive attributes or phantom data variants
//!   to user defined types. And also crate new types and implement block.

mod expand;
pub(crate) mod parse;

pub use parse::{composite::keyword::CompositeKeyword, Def};
use syn::spanned::Spanned;

mod keyword {
	syn::custom_keyword!(dev_mode);
}

pub fn pallet(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let mut dev_mode = false;
	if !attr.is_empty() {
		if let Ok(_) = syn::parse::<keyword::dev_mode>(attr.clone()) {
			dev_mode = true;
		} else {
			let msg = "Invalid pallet macro call: unexpected attribute. Macro call must be \
				bare, such as `#[frame_support::pallet]` or `#[pallet]`, or must specify the \
				`dev_mode` attribute, such as `#[frame_support::pallet(dev_mode)]` or \
				#[pallet(dev_mode)].";
			let span = proc_macro2::TokenStream::from(attr).span();
			return syn::Error::new(span, msg).to_compile_error().into()
		}
	}

	let item = syn::parse_macro_input!(item as syn::ItemMod);
	match parse::Def::try_from(item, dev_mode) {
		Ok(def) => expand::expand(def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
