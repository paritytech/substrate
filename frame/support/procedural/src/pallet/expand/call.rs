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
	pallet::{
		parse::call::{CallVariantDef, CallWeightDef},
		Def,
	},
	COUNTER,
};
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;

///
/// * Generate enum call and implement various trait on it.
/// * Implement Callable and call_function on `Pallet`
pub fn expand_call(def: &mut Def) -> proc_macro2::TokenStream {
	let (span, where_clause, methods, docs) = match def.call.as_ref() {
		Some(call) => {
			let span = call.attr_span;
			let where_clause = call.where_clause.clone();
			let methods = call.methods.clone();
			let docs = call.docs.clone();

			(span, where_clause, methods, docs)
		},
		None => (def.item.span(), def.config.where_clause.clone(), Vec::new(), Vec::new()),
	};
	let frame_support = &def.frame_support;
	let frame_system = &def.frame_system;
	let type_impl_gen = &def.type_impl_generics(span);
	let type_decl_bounded_gen = &def.type_decl_bounded_generics(span);
	let type_use_gen = &def.type_use_generics(span);
	let call_ident = syn::Ident::new("Call", span);
	let pallet_ident = &def.pallet_struct.pallet;

	let fn_name = methods.iter().map(|method| &method.name).collect::<Vec<_>>();
	let call_index = methods.iter().map(|method| method.call_index).collect::<Vec<_>>();
	let new_call_variant_fn_name = fn_name
		.iter()
		.map(|fn_name| quote::format_ident!("new_call_variant_{}", fn_name))
		.collect::<Vec<_>>();

	let new_call_variant_doc = fn_name
		.iter()
		.map(|fn_name| format!("Create a call with the variant `{}`.", fn_name))
		.collect::<Vec<_>>();

	let mut call_index_warnings = Vec::new();
	// Emit a warning for each call that is missing `call_index` when not in dev-mode.
	for method in &methods {
		if method.explicit_call_index || def.dev_mode {
			continue
		}

		let warning = proc_macro_warning::Warning::new_deprecated("ImplicitCallIndex")
			.index(call_index_warnings.len())
			.old("use implicit call indices")
			.new("ensure that all calls have a `pallet::call_index` attribute or put the pallet into `dev` mode")
			.help_links(&[
				"https://github.com/paritytech/substrate/pull/12891",
				"https://github.com/paritytech/substrate/pull/11381"
			])
			.span(method.name.span())
			.build();
		call_index_warnings.push(warning);
	}

	let mut fn_weight = Vec::<TokenStream2>::new();
	let mut weight_warnings = Vec::new();
	for method in &methods {
		match &method.weight {
			CallWeightDef::DevModeDefault => fn_weight.push(syn::parse_quote!(0)),
			CallWeightDef::Immediate(e @ syn::Expr::Lit(lit)) if !def.dev_mode => {
				let warning = proc_macro_warning::Warning::new_deprecated("ConstantWeight")
					.index(weight_warnings.len())
					.old("use hard-coded constant as call weight")
					.new("benchmark all calls or put the pallet into `dev` mode")
					.help_link("https://github.com/paritytech/substrate/pull/13798")
					.span(lit.span())
					.build();
				weight_warnings.push(warning);
				fn_weight.push(e.into_token_stream());
			},
			CallWeightDef::Immediate(e) => fn_weight.push(e.into_token_stream()),
			CallWeightDef::Inherited => {
				let pallet_weight = def
					.call
					.as_ref()
					.expect("we have methods; we have calls; qed")
					.inherited_call_weight
					.as_ref()
					.expect("the parser prevents this");

				// Expand `<<T as Config>::WeightInfo>::call_name()`.
				let t = &pallet_weight.typename;
				let n = &method.name;
				fn_weight.push(quote!({ < #t > :: #n ()	}));
			},
		}
	}
	debug_assert_eq!(fn_weight.len(), methods.len());

	let map_fn_docs = if !def.dev_mode {
		// Emit the [`Pallet::method`] documentation only for non-dev modes.
		|method: &CallVariantDef| {
			let reference = format!("See [`Pallet::{}`].", method.name);
			quote!(#reference)
		}
	} else {
		// For the dev-mode do not provide a documenation link as it will break the
		// `cargo doc` if the pallet is private inside a test.
		|method: &CallVariantDef| {
			let reference = format!("See `Pallet::{}`.", method.name);
			quote!(#reference)
		}
	};

	let fn_doc = methods.iter().map(map_fn_docs).collect::<Vec<_>>();

	let args_name = methods
		.iter()
		.map(|method| method.args.iter().map(|(_, name, _)| name.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_name_stripped = methods
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

	let args_type = methods
		.iter()
		.map(|method| method.args.iter().map(|(_, _, type_)| type_.clone()).collect::<Vec<_>>())
		.collect::<Vec<_>>();

	let args_compact_attr = methods.iter().map(|method| {
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

	let default_docs =
		[syn::parse_quote!(r"Contains a variant per dispatchable extrinsic that this pallet has.")];
	let docs = if docs.is_empty() { &default_docs[..] } else { &docs[..] };

	let maybe_compile_error = if def.call.is_none() {
		quote::quote! {
			compile_error!(concat!(
				"`",
				stringify!($pallet_name),
				"` does not have #[pallet::call] defined, perhaps you should remove `Call` from \
				construct_runtime?",
			));
		}
	} else {
		proc_macro2::TokenStream::new()
	};

	let count = COUNTER.with(|counter| counter.borrow_mut().inc());
	let macro_ident = syn::Ident::new(&format!("__is_call_part_defined_{}", count), span);

	let capture_docs = if cfg!(feature = "no-metadata-docs") { "never" } else { "always" };

	// Wrap all calls inside of storage layers
	if let Some(syn::Item::Impl(item_impl)) = def
		.call
		.as_ref()
		.map(|c| &mut def.item.content.as_mut().expect("Checked by def parser").1[c.index])
	{
		item_impl.items.iter_mut().for_each(|i| {
			if let syn::ImplItem::Fn(method) = i {
				let block = &method.block;
				method.block = syn::parse_quote! {{
					// We execute all dispatchable in a new storage layer, allowing them
					// to return an error at any point, and undoing any storage changes.
					#frame_support::storage::with_storage_layer(|| #block)
				}};
			}
		});
	}

	// Extracts #[allow] attributes, necessary so that we don't run into compiler warnings
	let maybe_allow_attrs = methods
		.iter()
		.map(|method| {
			method
				.attrs
				.iter()
				.find(|attr| attr.path().is_ident("allow"))
				.map_or(proc_macro2::TokenStream::new(), |attr| attr.to_token_stream())
		})
		.collect::<Vec<_>>();

	quote::quote_spanned!(span =>
		mod warnings {
			#(
				#call_index_warnings
			)*
			#(
				#weight_warnings
			)*
		}

		#[doc(hidden)]
		pub mod __substrate_call_check {
			#[macro_export]
			#[doc(hidden)]
			macro_rules! #macro_ident {
				($pallet_name:ident) => {
					#maybe_compile_error
				};
			}

			#[doc(hidden)]
			pub use #macro_ident as is_call_part_defined;
		}

		#( #[doc = #docs] )*
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
		pub enum #call_ident<#type_decl_bounded_gen> #where_clause {
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				#frame_support::sp_std::marker::PhantomData<(#type_use_gen,)>,
				#frame_support::Never,
			),
			#(
				#[doc = #fn_doc]
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

		impl<#type_impl_gen> #frame_support::dispatch::GetCallIndex for #call_ident<#type_use_gen>
			#where_clause
		{
			fn get_call_index(&self) -> u8 {
				match *self {
					#( Self::#fn_name { .. } => #call_index, )*
					Self::__Ignore(_, _) => unreachable!("__PhantomItem cannot be used."),
				}
			}

			fn get_call_indices() -> &'static [u8] {
				&[ #( #call_index, )* ]
			}
		}

		impl<#type_impl_gen> #frame_support::traits::UnfilteredDispatchable
			for #call_ident<#type_use_gen>
			#where_clause
		{
			type RuntimeOrigin = #frame_system::pallet_prelude::OriginFor<T>;
			fn dispatch_bypass_filter(
				self,
				origin: Self::RuntimeOrigin
			) -> #frame_support::dispatch::DispatchResultWithPostInfo {
				#frame_support::dispatch_context::run_in_context(|| {
					match self {
						#(
							Self::#fn_name { #( #args_name_pattern, )* } => {
								#frame_support::sp_tracing::enter_span!(
									#frame_support::sp_tracing::trace_span!(stringify!(#fn_name))
								);
								#maybe_allow_attrs
								<#pallet_ident<#type_use_gen>>::#fn_name(origin, #( #args_name, )* )
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

		impl<#type_impl_gen> #frame_support::dispatch::Callable<T> for #pallet_ident<#type_use_gen>
			#where_clause
		{
			type RuntimeCall = #call_ident<#type_use_gen>;
		}

		impl<#type_impl_gen> #pallet_ident<#type_use_gen> #where_clause {
			#[doc(hidden)]
			pub fn call_functions() -> #frame_support::metadata_ir::PalletCallMetadataIR {
				#frame_support::scale_info::meta_type::<#call_ident<#type_use_gen>>().into()
			}
		}
	)
}
