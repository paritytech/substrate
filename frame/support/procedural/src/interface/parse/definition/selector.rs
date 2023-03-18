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

pub enum Type {
	Default { return_ty: Box<syn::Type> },
	Named { name: syn::Ident, return_ty: Box<syn::Type> },
}

pub struct SelectorDef {
	default: SingleSelectorDef,
	others: Option<Vec<SingleSelectorDef>>,
}

impl SelectorDef {
	pub fn try_from(
		selectors: Option<SelectorDef>,
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::TraitItem,
	) -> syn::Result<Self> {
		todo!()
	}
}

pub struct SingleSelectorDef {
	/// Function name.
	name: syn::Ident,
	/// The return type of the selector.
	output: Box<syn::Type>,
	/// Docs, used for metadata.
	docs: Vec<syn::Lit>,
	/// Attributes annotated at the top of the selector function.
	attrs: Vec<syn::Attribute>,
	/// The span of the selector definition
	attr_span: proc_macro2::Span,
}

impl SingleSelectorDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		todo!()
	}
}
