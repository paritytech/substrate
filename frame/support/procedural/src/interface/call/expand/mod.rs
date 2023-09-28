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

use quote::ToTokens;

pub fn expand(mut def: super::parse::Def) -> proc_macro2::TokenStream {
	let indices = def.variants.iter().map(|var| var.index).collect::<Vec<_>>();
	let name = def.variants.iter().map(|var| var.name.clone()).collect::<Vec<_>>();
	let _inner_types = def.variants.iter().map(|var| var.inner.clone()).collect::<Vec<_>>();
	let frame_support = def.frame_support;
	let frame_system = def.frame_system;
	let sp_core = def.sp_core;
	let enum_name = def.item.ident.clone();
	let runtime = def.runtime.clone();

	def.item
		.variants
		.iter_mut()
		.zip(indices)
		.for_each(|(var, index)| var.attrs.push(syn::parse_quote!(#[codec(index = #index)])));

	def.item.attrs.push(syn::parse_quote!(#[derive(
			#frame_support::RuntimeDebugNoBound,
			#frame_support::CloneNoBound,
			#frame_support::EqNoBound,
			#frame_support::PartialEqNoBound,
			#frame_support::codec::Encode,
			#frame_support::codec::Decode,
			#frame_support::scale_info::TypeInfo,)]));

	let impl_item = quote::quote_spanned!(def.span =>

		impl  #frame_support::dispatch::GetDispatchInfo for #enum_name {
			fn get_dispatch_info(&self) -> #frame_support::dispatch::DispatchInfo {
				todo!()
			}
		}


		impl #frame_support::traits::UnfilteredDispatchable
			for #enum_name
		{
			type RuntimeOrigin = <#runtime as #frame_system::Config>::RuntimeOrigin;

			fn dispatch_bypass_filter(
				self,
				origin: Self::RuntimeOrigin,
			) -> #frame_support::dispatch::DispatchResultWithPostInfo {
				#frame_support::dispatch_context::run_in_context(|| {
					match self {
						#(
							Self::#name(interface) => {
								#frame_support::sp_tracing::enter_span!(
									#frame_support::sp_tracing::trace_span!(stringify!(#name))
								);

								#frame_support::traits::UnfilteredDispatchable::dispatch_bypass_filter(interface, origin)
									.map(Into::into).map_err(Into::into)
							},
						)*
					}
				})
			}
		}



		impl #frame_support::traits::GetCallMetadata for #enum_name {
			fn get_module_names() -> &'static [&'static str] {
				todo!()
			}

			fn get_call_names(module: &str) -> &'static [&'static str] {
				todo!()
			}

			fn get_call_metadata(&self) -> #frame_support::traits::CallMetadata {
				todo!()
			}
		}


		// Evaluate if the given index actually matches the standard defined index and trigger
		// a warning otherwise.
		const _: () = {

		};
	);

	let enum_item = def.item.into_token_stream();

	quote::quote!(
		#enum_item

		#impl_item
	)
}
