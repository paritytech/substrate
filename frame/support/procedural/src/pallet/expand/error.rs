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

use crate::{
	pallet::{parse::error::VariantField, Def},
	COUNTER,
};
use frame_support_procedural_tools::get_doc_literals;
use syn::spanned::Spanned;

///
/// * impl various trait on Error
pub fn expand_error(def: &mut Def) -> proc_macro2::TokenStream {
	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let error_token_unique_id =
		syn::Ident::new(&format!("__tt_error_token_{}", count), def.item.span());

	let frame_support = &def.frame_support;
	let frame_system = &def.frame_system;
	let config_where_clause = &def.config.where_clause;

	let error = if let Some(error) = &def.error {
		error
	} else {
		return quote::quote! {
			#[macro_export]
			#[doc(hidden)]
			macro_rules! #error_token_unique_id {
				{
					$caller:tt
					frame_support = [{ $($frame_support:ident)::* }]
				} => {
					$($frame_support::)*tt_return! {
						$caller
					}
				};
			}

			pub use #error_token_unique_id as tt_error_token;
		}
	};

	let error_ident = &error.error;
	let type_impl_gen = &def.type_impl_generics(error.attr_span);
	let type_use_gen = &def.type_use_generics(error.attr_span);

	let phantom_variant: syn::Variant = syn::parse_quote!(
		#[doc(hidden)]
		#[codec(skip)]
		__Ignore(
			#frame_support::sp_std::marker::PhantomData<(#type_use_gen)>,
			#frame_support::Never,
		)
	);

	let as_str_matches = error.variants.iter().map(|(variant, field_ty, _)| {
		let variant_str = variant.to_string();
		match field_ty {
			Some(VariantField { is_named: true }) => {
				quote::quote_spanned!(error.attr_span => Self::#variant { .. } => #variant_str,)
			},
			Some(VariantField { is_named: false }) => {
				quote::quote_spanned!(error.attr_span => Self::#variant(..) => #variant_str,)
			},
			None => {
				quote::quote_spanned!(error.attr_span => Self::#variant => #variant_str,)
			},
		}
	});

	let error_item = {
		let item = &mut def.item.content.as_mut().expect("Checked by def parser").1[error.index];
		if let syn::Item::Enum(item) = item {
			item
		} else {
			unreachable!("Checked by error parser")
		}
	};

	error_item.variants.insert(0, phantom_variant);

	let capture_docs = if cfg!(feature = "no-metadata-docs") { "never" } else { "always" };

	// derive TypeInfo for error metadata
	error_item.attrs.push(syn::parse_quote! {
		#[derive(
			#frame_support::codec::Encode,
			#frame_support::codec::Decode,
			#frame_support::scale_info::TypeInfo,
			#frame_support::PalletError,
		)]
	});
	error_item.attrs.push(syn::parse_quote!(
		#[scale_info(skip_type_params(#type_use_gen), capture_docs = #capture_docs)]
	));

	if get_doc_literals(&error_item.attrs).is_empty() {
		error_item.attrs.push(syn::parse_quote!(
			#[doc = r"
			Custom [dispatch errors](https://docs.substrate.io/main-docs/build/events-errors/)
			of this pallet.
			"]
		));
	}

	quote::quote_spanned!(error.attr_span =>
		impl<#type_impl_gen> #frame_support::sp_std::fmt::Debug for #error_ident<#type_use_gen>
			#config_where_clause
		{
			fn fmt(&self, f: &mut #frame_support::sp_std::fmt::Formatter<'_>)
				-> #frame_support::sp_std::fmt::Result
			{
				f.write_str(self.as_str())
			}
		}

		impl<#type_impl_gen> #error_ident<#type_use_gen> #config_where_clause {
			#[doc(hidden)]
			pub fn as_str(&self) -> &'static str {
				match &self {
					Self::__Ignore(_, _) => unreachable!("`__Ignore` can never be constructed"),
					#( #as_str_matches )*
				}
			}
		}

		impl<#type_impl_gen> From<#error_ident<#type_use_gen>> for &'static str
			#config_where_clause
		{
			fn from(err: #error_ident<#type_use_gen>) -> &'static str {
				err.as_str()
			}
		}

		impl<#type_impl_gen> From<#error_ident<#type_use_gen>>
			for #frame_support::sp_runtime::DispatchError
			#config_where_clause
		{
			fn from(err: #error_ident<#type_use_gen>) -> Self {
				use #frame_support::codec::Encode;
				let index = <
					<T as #frame_system::Config>::PalletInfo
					as #frame_support::traits::PalletInfo
				>::index::<Pallet<#type_use_gen>>()
					.expect("Every active module has an index in the runtime; qed") as u8;
				let mut encoded = err.encode();
				encoded.resize(#frame_support::MAX_MODULE_ERROR_ENCODED_SIZE, 0);

				#frame_support::sp_runtime::DispatchError::Module(#frame_support::sp_runtime::ModuleError {
					index,
					error: TryInto::try_into(encoded).expect("encoded error is resized to be equal to the maximum encoded error size; qed"),
					message: Some(err.as_str()),
				})
			}
		}

		#[macro_export]
		#[doc(hidden)]
		macro_rules! #error_token_unique_id {
			{
				$caller:tt
				frame_support = [{ $($frame_support:ident)::* }]
			} => {
				$($frame_support::)*tt_return! {
					$caller
					error = [{ #error_ident }]
				}
			};
		}

		pub use #error_token_unique_id as tt_error_token;
	)
}
