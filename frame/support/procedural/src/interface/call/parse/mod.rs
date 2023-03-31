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

use frame_support_procedural_tools::generate_crate_access_2018;
use syn::spanned::Spanned;

pub struct Def {
	pub item: syn::ItemEnum,
	pub frame_support: syn::Ident,
}
impl Def {
	pub fn try_from(mut item: syn::ItemEnum) -> syn::Result<Self> {
		let item_span = item.span();
		let frame_support = generate_crate_access_2018("frame-support")?;

		todo!()
	}
}
