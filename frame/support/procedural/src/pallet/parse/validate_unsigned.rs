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

use syn::spanned::Spanned;
use super::helper;

/// The definition of the pallet validate unsigned implementation.
pub struct ValidateUnsignedDef {
	/// The index of validate unsigned item in pallet module.
	pub index: usize,
	/// A set of usage of instance, must be check for consistency with config.
	pub instances: Vec<helper::InstanceUsage>,
}

impl ValidateUnsignedDef {
	pub fn try_from(index: usize, item: &mut syn::Item) -> syn::Result<Self> {
		let item = if let syn::Item::Impl(item) = item {
			item
		} else {
			let msg = "Invalid pallet::validate_unsigned, expected item impl";
			return Err(syn::Error::new(item.span(), msg));
		};

		if item.trait_.is_none() {
			let msg = "Invalid pallet::validate_unsigned, expected impl<..> ValidateUnsigned for \
				Pallet<..>";
			return Err(syn::Error::new(item.span(), msg));
		}

		if let Some(last) = item.trait_.as_ref().unwrap().1.segments.last() {
			if last.ident != "ValidateUnsigned" {
				let msg = "Invalid pallet::validate_unsigned, expected trait ValidateUnsigned";
				return Err(syn::Error::new(last.span(), msg));
			}
		} else {
			let msg = "Invalid pallet::validate_unsigned, expected impl<..> ValidateUnsigned for \
				Pallet<..>";
			return Err(syn::Error::new(item.span(), msg));
		}

		let mut instances = vec![];
		instances.push(helper::check_pallet_struct_usage(&item.self_ty)?);
		instances.push(helper::check_impl_gen(&item.generics, item.impl_token.span())?);

		Ok(ValidateUnsignedDef { index, instances })
	}
}
