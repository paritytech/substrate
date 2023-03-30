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

use crate::interface::parse::Def;

// TODO: REMOVE
/*
struct DefaultSelector<Runtime>(std::marker::PhantomData<Runtime>);
struct RestrictedCurrency<Runtime>(std::marker::PhantomData<Runtime>);

impl<Runtime: Pip20> #frame_support::interface::Selector for DefaultSelector<Runtime> {
type Selected = <Runtime as Pip20>::Currency;

fn select(&self, from: sp_core::H256) -> SelectorResult<Self::Selected> {
todo!();
}
}
impl<Runtime> DefaultSelector<Runtime> {
	pub fn new() -> Self {
		DefaultSelector(Default::default())
	}
}
impl<Runtime: Pip20> #frame_support::interface::Selector for RestrictedCurrency<Runtime> {
type Selected = <Runtime as Pip20>::Currency;

fn select(&self, from: sp_core::H256) -> SelectorResult<Self::Selected> {
todo!();
}
}
impl<Runtime> RestrictedCurrency<Runtime> {
	pub fn new() -> Self {
		RestrictedCurrency(Default::default())
	}
}
// TODO: TILL HERE
 */
pub fn expand(def: &Def) -> proc_macro2::TokenStream {
	let (span, where_clause, selectors) = def.interface.selectors();

	let frame_support = &def.frame_support;
	let trait_name = &def.interface.trait_name;

	let mut selector_names_and_return = selectors
		.iter()
		.map(|selector| (selector.name.clone(), selector.method.clone(), selector.selected.clone()))
		.collect::<Vec<_>>();

	let default = selectors
		.iter()
		.filter(|selector| selector.default)
		.map(|selector| (selector.method.clone(), selector.selected.clone()))
		.collect::<Vec<_>>();
	if let Some((method, selected)) = default.first() {
		selector_names_and_return.push((
			syn::Ident::new("DefaultSelector", span),
			method.clone(),
			selected.clone(),
		))
	}

	let name = selector_names_and_return
		.iter()
		.map(|(name, _, _)| name.clone())
		.collect::<Vec<_>>();
	let selected = selector_names_and_return
		.iter()
		.map(|(_, _, selected)| selected.clone())
		.collect::<Vec<_>>();
	let method = selector_names_and_return
		.iter()
		.map(|(_, method, _)| method.clone())
		.collect::<Vec<_>>();

	quote::quote_spanned!(span =>
		#(
			struct #name<Runtime>(#frame_support::sp_std::marker::PhantomData<Runtime>);

			impl<Runtime> #name<Runtime> {
				pub fn new() -> Self {
				 #name(Default::default())
				}
			}

			impl<Runtime: #trait_name> #frame_support::interface::Selector for #name<Runtime> #where_clause{
				type Selected = #selected;

				fn select(&self, from: sp_core::H256) -> SelectorResult<Self::Selected> {
					Runtime::#method(from)
				}
			}
		)*
	)
}
