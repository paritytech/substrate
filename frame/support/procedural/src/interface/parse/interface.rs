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

pub struct InterfaceDef {
	item: syn::ItemTrait,
	selectors: Option<SelectorDef>,
	views: Option<Vec<ViewDef>>,
	calls: Option<Vec<CallDef>>,
}

impl InterfaceDef {
	fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		// Ensure NO generics or where clauses on interface trait
		let item_span = item.span();
		if !item.generics == Generics::default() {
			// TODO: Where clauses should be allowed. We can carry them to all impl blocks.
			//       But "extending" an interface gets harder, as carrying them over from
			//       extended traits is harder.
			let msg = "Invalid Interface definition. Traits that define an interface \
                currently can not have generics or where clauses.";
			return Err(syn::Error::new(item_span, msg))
		}

		// Filter selector methods
		let with_selector = false;

		// Filter view methods

		// Filter call methods
		todo!()
	}
}

struct ViewDef {
	views: Vec<syn::TraitItemMethod>,
}

impl ViewDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}

struct CallDef {
	calls: Vec<syn::TraitItemMethod>,
}

impl CallDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}
