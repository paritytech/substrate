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

use crate::interface::definition::parse::Def;
use quote::ToTokens;
use syn::spanned::Spanned;

pub fn expand(def: &Def) -> proc_macro2::TokenStream {
	let (span, where_clause, calls) = def.interface.calls();

	let frame_support = &def.frame_support;
	let frame_system = &def.frame_system;
	let call_ident = syn::Ident::new("Call", span);

	let fn_name = calls.iter().map(|method| &method.name).collect::<Vec<_>>();
	let call_index = calls.iter().map(|method| method.call_index).collect::<Vec<_>>();
	let new_call_variant_fn_name = fn_name
		.iter()
		.map(|fn_name| quote::format_ident!("new_call_variant_{}", fn_name))
		.collect::<Vec<_>>();
	let new_call_variant_doc = fn_name
		.iter()
		.map(|fn_name| format!("Create a call with the variant `{}`.", fn_name))
		.collect::<Vec<_>>();

	let interface_trait_name = def.interface.trait_name.clone();

	let type_impl_gen = quote::quote_spanned!(span => Runtime: #interface_trait_name);
	let type_use_gen = quote::quote_spanned!(span => Runtime);

	let fn_weight = calls.iter().map(|method| &method.weight);
	let fn_doc = calls.iter().map(|method| &method.docs).collect::<Vec<_>>();

	let args_name = calls
		.iter()
		.map(|method| method.args.iter().map(|(_, name, _)| name.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_name_stripped = calls
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

	let args_type = calls
		.iter()
		.map(|method| method.args.iter().map(|(_, _, type_)| type_.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_compact_attr = calls.iter().map(|method| {
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

	// Extracts #[allow] attributes, necessary so that we don't run into compiler warnings
	let maybe_allow_attrs = calls
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
		pub enum #call_ident<#type_impl_gen> #where_clause {
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				#frame_support::sp_std::marker::PhantomData<(#type_use_gen)>,
				#frame_support::Never,
			),
			#(
				#( #[doc = #fn_doc] )*
				#[codec(index = #call_index)]
				#fn_name {
					#(
						#[allow(missing_docs)]
						#args_compact_attr #args_name_stripped: #args_type
					),*
				},
			)*
		}

		impl<#type_impl_gen> #call_ident<#type_use_gen> #where_clause {
			#(
				#[doc = #new_call_variant_doc]
				pub fn #new_call_variant_fn_name(
					#( #args_name_stripped: #args_type ),*
				) -> Self {
					Self::#fn_name {
						#( #args_name_stripped ),*
					}
				}
			)*
		}

		impl<#type_impl_gen> #frame_support::dispatch::GetDispatchInfo
			for #call_ident<#type_use_gen>
			#where_clause
		{
			fn get_dispatch_info(&self) -> #frame_support::dispatch::DispatchInfo {
				match *self {
					#(
						Self::#fn_name { #( #args_name_pattern_ref, )* } => {
							let __pallet_base_weight = #fn_weight;

							let __pallet_weight = <
								dyn #frame_support::dispatch::WeighData<( #( & #args_type, )* )>
							>::weigh_data(&__pallet_base_weight, ( #( #args_name, )* ));

							let __pallet_class = <
								dyn #frame_support::dispatch::ClassifyDispatch<
									( #( & #args_type, )* )
								>
							>::classify_dispatch(&__pallet_base_weight, ( #( #args_name, )* ));

							let __pallet_pays_fee = <
								dyn #frame_support::dispatch::PaysFee<( #( & #args_type, )* )>
							>::pays_fee(&__pallet_base_weight, ( #( #args_name, )* ));

							#frame_support::dispatch::DispatchInfo {
								weight: __pallet_weight,
								class: __pallet_class,
								pays_fee: __pallet_pays_fee,
							}
						},
					)*
					Self::__Ignore(_, _) => unreachable!("__Ignore cannot be used"),
				}
			}
		}

		// Deprecated, but will warn when used
		#[allow(deprecated)]
		impl<#type_impl_gen> #frame_support::weights::GetDispatchInfo for #call_ident<#type_use_gen> #where_clause {}

		impl<#type_impl_gen> #frame_support::dispatch::GetCallName for #call_ident<#type_use_gen>
			#where_clause
		{
			fn get_call_name(&self) -> &'static str {
				match *self {
					#( Self::#fn_name { .. } => stringify!(#fn_name), )*
					Self::__Ignore(_, _) => unreachable!("__PhantomItem cannot be used."),
				}
			}

			fn get_call_names() -> &'static [&'static str] {
				&[ #( stringify!(#fn_name), )* ]
			}
		}


		impl<#type_impl_gen> #frame_support::traits::UnfilteredDispatchable
			for #call_ident<#type_use_gen>
			#where_clause
		{
			type RuntimeOrigin = <#type_use_gen as #frame_system::Config>::RuntimeOrigin;

			fn dispatch_bypass_filter(
				self,
				origin: Self::RuntimeOrigin,
			) -> #frame_support::dispatch::DispatchResultWithPostInfo {
				#frame_support::dispatch_context::run_in_context(|| {
					match self {
						#(
							Self::#fn_name { #( #args_name_pattern, )* } => {
								#frame_support::sp_tracing::enter_span!(
									#frame_support::sp_tracing::trace_span!(stringify!(#fn_name))
								);

								#maybe_allow_attrs
								<#type_use_gen as #interface_trait_name>::#fn_name(origin, #( #args_name, )* )
									.map(Into::into).map_err(Into::into)
							},
						)*
						Self::__Ignore(_, _) => {
							let _ = origin; // Use origin for empty Call enum
							unreachable!("__PhantomItem cannot be used.");
						},
					}
				})
			}
		}

		impl<#type_impl_gen> #call_ident<#type_use_gen> #where_clause {
			#[doc(hidden)]
			pub fn call_functions() -> #frame_support::metadata::PalletCallMetadata {
				#frame_support::scale_info::meta_type::<#call_ident<#type_use_gen>>().into()
			}
		}
	)
}
