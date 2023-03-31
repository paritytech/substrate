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

use crate::interface::definition::{parse::Def, SelectorType};
use quote::ToTokens;
use syn::spanned::Spanned;

pub fn expand(def: &Def) -> proc_macro2::TokenStream {
	let (span, where_clause, views) = def.interface.views();

	let frame_support = &def.frame_support;
	let sp_core = &def.sp_core;
	let view_ident = syn::Ident::new("View", span);

	let fn_name = views.iter().map(|method| &method.name).collect::<Vec<_>>();
	let view_index = views.iter().map(|method| method.view_index).collect::<Vec<_>>();
	let new_view_variant_fn_name = fn_name
		.iter()
		.map(|fn_name| quote::format_ident!("new_view_variant_{}", fn_name))
		.collect::<Vec<_>>();
	let new_view_variant_doc = fn_name
		.iter()
		.map(|fn_name| format!("Create a view with the variant `{}`.", fn_name))
		.collect::<Vec<_>>();

	let interface_trait_name = def.interface.trait_name.clone();

	let type_impl_gen = quote::quote_spanned!(span => Runtime: #interface_trait_name);
	let type_use_gen = quote::quote_spanned!(span => Runtime);
	let type_decl_gen = quote::quote_spanned!(span => Runtime);

	let fn_doc = views.iter().map(|method| &method.docs).collect::<Vec<_>>();

	let args_name = views
		.iter()
		.map(|method| method.args.iter().map(|(_, name, _)| name.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_name_stripped = views
		.iter()
		.map(|method| {
			method
				.args
				.iter()
				.map(|(_, name, _)| {
					syn::Ident::new(name.to_string().trim_start_matches('_'), name.span())
				})
				.collect::<Vec<_>>()
		})
		.collect::<Vec<_>>();

	let make_args_name_pattern = |ref_tok| {
		args_name
			.iter()
			.zip(args_name_stripped.iter())
			.map(|(args_name, args_name_stripped)| {
				args_name
					.iter()
					.zip(args_name_stripped)
					.map(|(args_name, args_name_stripped)| {
						if args_name == args_name_stripped {
							quote::quote!( #ref_tok #args_name )
						} else {
							quote::quote!( #args_name_stripped: #ref_tok #args_name )
						}
					})
					.collect::<Vec<_>>()
			})
			.collect::<Vec<_>>()
	};

	let args_name_pattern = make_args_name_pattern(None);
	let args_name_pattern_ref = make_args_name_pattern(Some(quote::quote!(ref)));
	let capture_docs = if cfg!(feature = "no-metadata-docs") { "never" } else { "always" };

	let args_type = views
		.iter()
		.map(|method| method.args.iter().map(|(_, _, type_)| type_.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_compact_attr = views.iter().map(|method| {
		method
			.args
			.iter()
			.map(|(is_compact, _, type_)| {
				if *is_compact {
					quote::quote_spanned!(type_.span() => #[codec(compact)] )
				} else {
					quote::quote!()
				}
			})
			.collect::<Vec<_>>()
	});

	let select_def = views
		.iter()
		.map(|method| match method.selector.as_ref() {
			Some(selector_type) => match selector_type {
				SelectorType::Default { .. } => {
					quote::quote!(
						let select = #frame_support::interface::Select::new(selectable, Box::new(DefaultSelector::<#type_use_gen>::new()));
					)
				},
				SelectorType::Named { name, .. } => {
					let name = name.clone();
					quote::quote_spanned!(method.attr_span =>
						let select = #frame_support::interface::Select::new(selectable, Box::new(#name::<#type_use_gen>::new()));
					)
				},
			},
			None => {
				quote::quote!(
					let select = #frame_support::interface::Select::new(selectable, Box::new(#frame_support::interface::EmptySelector::new()));
					select.select()?;
				)
			},
		})
		.collect::<Vec<_>>();

	let first_args_def = views
		.iter()
		.map(|method| match method.selector.as_ref() {
			Some(_selector_type) => {
				quote::quote!(select,)
			},
			None => {
				quote::quote!()
			},
		})
		.collect::<Vec<_>>();

	// Extracts #[allow] attributes, necessary so that we don't run into compiler warnings
	let maybe_allow_attrs = views
		.iter()
		.map(|method| {
			method
				.attrs
				.iter()
				.find(|attr| {
					if let Ok(syn::Meta::List(syn::MetaList { path, .. })) = attr.parse_meta() {
						path.segments.last().map(|seg| seg.ident == "allow").unwrap_or(false)
					} else {
						false
					}
				})
				.map_or(proc_macro2::TokenStream::new(), |attr| attr.to_token_stream())
		})
		.collect::<Vec<_>>();

	quote::quote_spanned!(span =>
		#[derive(
			#frame_support::RuntimeDebugNoBound,
			#frame_support::CloneNoBound,
			#frame_support::EqNoBound,
			#frame_support::PartialEqNoBound,
			#frame_support::codec::Encode,
			#frame_support::codec::Decode,
			#frame_support::scale_info::TypeInfo,
		)]
		#[codec(encode_bound())]
		#[codec(decode_bound())]
		#[scale_info(skip_type_params(#type_use_gen), capture_docs = #capture_docs)]
		#[allow(non_camel_case_types)]
		pub enum #view_ident<#type_impl_gen> #where_clause {
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				#frame_support::sp_std::marker::PhantomData<(#type_use_gen)>,
				#frame_support::Never,
			),
			#(
				#( #[doc = #fn_doc] )*
				#[codec(index = #view_index)]
				#fn_name {
					#(
						#[allow(missing_docs)]
						#args_compact_attr #args_name_stripped: #args_type
					),*
				},
			)*
		}

		impl<#type_impl_gen> #view_ident<#type_use_gen> #where_clause {
			#(
				#[doc = #new_view_variant_doc]
				pub fn #new_view_variant_fn_name(
					#( #args_name_stripped: #args_type ),*
				) -> Self {
					Self::#fn_name {
						#( #args_name_stripped ),*
					}
				}
			)*
		}

		impl<#type_impl_gen> #frame_support::interface::View
			for #view_ident<#type_use_gen>
			#where_clause
		{
			fn view(
				self,
				selectable: sp_core::H256,
			) -> #frame_support::interface::ViewResult<Vec<u8>> {
					match self {
						#(
							Self::#fn_name { #( #args_name_pattern, )* } => {
								#frame_support::sp_tracing::enter_span!(
									#frame_support::sp_tracing::trace_span!(stringify!(#fn_name))
								);

								#maybe_allow_attrs
								#select_def
								<#type_use_gen as #interface_trait_name>::#fn_name(#first_args_def #( #args_name, )* )
									.map(|ty| #frame_support::codec::Encode::encode(&ty)).map_err(Into::into)
							},
						)*
						Self::__Ignore(_, _) => {
							let _ = selectable; // Use selectable for empty view enum
							unreachable!("__PhantomItem cannot be used.");
						},
					}
			}
		}

		impl<#type_impl_gen> #view_ident<#type_use_gen> #where_clause {
			#[doc(hidden)]
			pub fn call_functions() -> #frame_support::metadata::PalletCallMetadata {
				#frame_support::scale_info::meta_type::<#view_ident<#type_use_gen>>().into()
			}
		}
	)
}
