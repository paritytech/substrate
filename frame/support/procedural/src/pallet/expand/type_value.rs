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

use crate::pallet::Def;

///
/// * Generate the struct
/// * implement the `Get<..>` on it
/// * Rename the name of the function to internal name
pub fn expand_type_values(def: &mut Def) -> proc_macro2::TokenStream {
	let mut expand = quote::quote!();
	let frame_support = &def.frame_support;

	for type_value in &def.type_values {
		let fn_name_str = &type_value.ident.to_string();
		let fn_name_snakecase = inflector::cases::snakecase::to_snake_case(fn_name_str);
		let fn_ident_renamed = syn::Ident::new(
			&format!("__type_value_for_{}", fn_name_snakecase),
			type_value.ident.span(),
		);

		let type_value_item = {
			let item = &mut def.item.content.as_mut().expect("Checked by def").1[type_value.index];
			if let syn::Item::Fn(item) = item {
				item
			} else {
				unreachable!("Checked by error parser")
			}
		};

		// Rename the type_value function name
		type_value_item.sig.ident = fn_ident_renamed.clone();

		let vis = &type_value.vis;
		let ident = &type_value.ident;
		let type_ = &type_value.type_;
		let where_clause = &type_value.where_clause;

		let (struct_impl_gen, struct_use_gen) = if type_value.is_generic {
			(
				def.type_impl_generics(type_value.attr_span),
				def.type_use_generics(type_value.attr_span),
			)
		} else {
			(Default::default(), Default::default())
		};

		expand.extend(quote::quote_spanned!(type_value.attr_span =>
			#vis struct #ident<#struct_use_gen>(core::marker::PhantomData<((), #struct_use_gen)>);
			impl<#struct_impl_gen> #frame_support::traits::Get<#type_> for #ident<#struct_use_gen>
			#where_clause
			{
				fn get() -> #type_ {
					#fn_ident_renamed::<#struct_use_gen>()
				}
			}
		));
	}
	expand
}
