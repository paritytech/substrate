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
// limitations under the License

use crate::construct_bundle::Pallet;
use proc_macro2::TokenStream;
use quote::quote;
use std::str::FromStr;
use syn::Ident;

pub fn expand_outer_dispatch(
	runtime: &Ident,
	// system_pallet: &Pallet,
	pallet_decls: &[Pallet],
	scrate: &TokenStream,
) -> TokenStream {
	let mut variant_defs = TokenStream::new();
	let mut variant_patterns = Vec::new();
	let mut query_call_part_macros = Vec::new();
	let mut pallet_names = Vec::new();
	let mut pallet_attrs = Vec::new();
	// let system_path = &system_pallet.path;

	let pallets_with_call = pallet_decls.iter().filter(|decl| decl.exists_part("Call"));

	let type_impl_gen = quote!(T: Config);
	let type_use_gen = quote!(T);

	for pallet_declaration in pallets_with_call {
		let name = &pallet_declaration.name;
		let path = &pallet_declaration.path;
		let index = pallet_declaration.index;
		let attr =
			pallet_declaration.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
				let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
					.expect("was successfully parsed before; qed");
				quote! {
					#acc
					#attr
				}
			});

		variant_defs.extend(quote! {
			#attr
			#[codec(index = #index)]
			#name( #scrate::dispatch::CallableCallFor<#name<T>, Pallet<T>> ),
		});
		variant_patterns.push(quote!(Call::<T>::#name(call)));
		pallet_names.push(name);
		pallet_attrs.push(attr);
		query_call_part_macros.push(quote! {
			#path::__substrate_call_check::is_call_part_defined!(#name);
		});
	}

	quote! {
		#( #query_call_part_macros )*

		#[derive(
			#scrate::CloneNoBound, 
			#scrate::PartialEqNoBound, 
			#scrate::EqNoBound,
			#scrate::codec::Encode,
			#scrate::codec::Decode,
			#scrate::scale_info::TypeInfo,
			#scrate::RuntimeDebugNoBound,
		)]
		#[codec(encode_bound())]
		#[codec(decode_bound())]
		#[scale_info(skip_type_params(#type_use_gen), capture_docs = "never")]
		pub enum Call<#type_impl_gen> {
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				#scrate::sp_std::marker::PhantomData<(T,)>,
				#scrate::Never,
			),
			#variant_defs
		}

		impl<#type_impl_gen> #scrate::dispatch::Callable<T> for Pallet<T>
		{
			type RuntimeCall = Call<#type_use_gen>;
		}

				
		impl<#type_impl_gen> #scrate::dispatch::Callable<Pallet<T>> for pallet_template::Pallet<T>
		{
			type RuntimeCall = pallet_template::Call<Pallet<T>>;
		}
		
		impl<#type_impl_gen> #scrate::dispatch::Callable<Pallet<T>> for pallet_template_2::Pallet<T>
		{
			type RuntimeCall = pallet_template_2::Call<Pallet<T>>;
		}

		impl<#type_impl_gen> #scrate::dispatch::GetDispatchInfo for Call<T> {
			fn get_dispatch_info(&self) -> #scrate::dispatch::DispatchInfo {
				match self {
					#(
						#pallet_attrs
						#variant_patterns => call.get_dispatch_info(),
					)*
					Self::__Ignore(_, _) => unreachable!("__Ignore cannot be used"),
				}
			}
		}
		// Deprecated, but will warn when used
		#[allow(deprecated)]
		impl<#type_impl_gen> #scrate::weights::GetDispatchInfo for Call<T> {}

		impl<#type_impl_gen> #scrate::dispatch::GetCallName for Call<T>
		{
			fn get_call_name(&self) -> &'static str {
				match self {
					#(
						#pallet_attrs
						#variant_patterns => call.get_call_name(),
					)*
					Self::__Ignore(_, _) => unreachable!("__PhantomItem cannot be used."),
				}
			}

			fn get_call_names() -> &'static [&'static str] {
				// &[ #( stringify!(#fn_name), )* ]
				&[ ]
			}
		}

		impl<#type_impl_gen> #scrate::dispatch::GetCallIndex for Call<T>
		{
			fn get_call_index(&self) -> u8 {
				match self {
					#(
						#pallet_attrs
						#variant_patterns => call.get_call_index(),
					)*
					Self::__Ignore(_, _) => unreachable!("__PhantomItem cannot be used."),
				}
			}

			fn get_call_indices() -> &'static [u8] {
				// &[ #( #call_index, )* ]
				&[ ]
			}
		}

		impl<#type_impl_gen> #scrate::dispatch::GetCallMetadata for Call<T> {
			fn get_call_metadata(&self) -> #scrate::dispatch::CallMetadata {
				use #scrate::dispatch::GetCallName;
				match self {
					#(
						#pallet_attrs
						#variant_patterns => {
							let function_name = call.get_call_name();
							let pallet_name = stringify!(#pallet_names);
							#scrate::dispatch::CallMetadata { function_name, pallet_name }
						}
					)*
					_ => unreachable!(),
				}
			}

			fn get_module_names() -> &'static [&'static str] {
				&[#(
					#pallet_attrs
					stringify!(#pallet_names),
				)*]
			}

			fn get_call_names(module: &str) -> &'static [&'static str] {
				use #scrate::dispatch::{Callable, GetCallName};
				match module {
					#(
						#pallet_attrs
						stringify!(#pallet_names) =>
							<<#pallet_names<T> as Callable<Pallet<T>>>::RuntimeCall
								as GetCallName>::get_call_names(),
					)*
					_ => unreachable!(),
				}
			}
		}

		// impl<#type_impl_gen> #scrate::dispatch::Dispatchable for Call<T> {
		// 	type RuntimeOrigin = frame_system::pallet_prelude::OriginFor<T>;
		// 	type Config = Call<T>;
		// 	type Info = #scrate::dispatch::DispatchInfo;
		// 	type PostInfo = #scrate::dispatch::PostDispatchInfo;
		// 	fn dispatch(self, origin: Self::RuntimeOrigin) -> #scrate::dispatch::DispatchResultWithPostInfo {
		// 		// if !<Self::RuntimeOrigin as #scrate::traits::OriginTrait>::filter_call(&origin, &self) {
		// 		// 	return #scrate::sp_std::result::Result::Err(
		// 		// 		#system_path::Error::<#runtime>::CallFiltered.into()
		// 		// 	);
		// 		// }

		// 		#scrate::traits::UnfilteredDispatchable::dispatch_bypass_filter(self, origin)
		// 	}
		// }

		impl<#type_impl_gen> #scrate::traits::UnfilteredDispatchable for Call<T> {
			type RuntimeOrigin = frame_system::pallet_prelude::OriginFor<T>;
			fn dispatch_bypass_filter(self, origin: Self::RuntimeOrigin) -> #scrate::dispatch::DispatchResultWithPostInfo {
				match self {
					#(
						#pallet_attrs
						#variant_patterns =>
							#scrate::traits::UnfilteredDispatchable::dispatch_bypass_filter(call, origin),
					)*
					Self::__Ignore(_, _) => {
						let _ = origin; // Use origin for empty Call enum
						unreachable!("__PhantomItem cannot be used.");
					},
				}
			}
		}

		// // #(
		// // 	#pallet_attrs
		// // 	impl<#type_impl_gen> #scrate::traits::IsSubType<#scrate::dispatch::CallableCallFor<#pallet_names<#type_use_gen>, #runtime<#type_use_gen>>> for <T as frame_system::Config>::RuntimeCall {
		// // 		#[allow(unreachable_patterns)]
		// // 		fn is_sub_type(&self) -> Option<&#scrate::dispatch::CallableCallFor<#pallet_names<#type_use_gen>, #runtime<#type_use_gen>>> {
		// // 			match self {
		// // 				#variant_patterns => Some(call),
		// // 				// May be unreachable
		// // 				_ => None,
		// // 			}
		// // 		}
		// // 	}

		// // 	#pallet_attrs
		// // 	impl<#type_impl_gen> From<#scrate::dispatch::CallableCallFor<#pallet_names<#type_use_gen>, #runtime<#type_use_gen>>> for <T as frame_system::Config>::RuntimeCall {
		// // 		fn from(call: #scrate::dispatch::CallableCallFor<#pallet_names<#type_use_gen>, #runtime<#type_use_gen>>) -> Self {
		// // 			#variant_patterns
		// // 		}
		// // 	}
		// // )*

		impl<#type_impl_gen> Pallet<T> {
			#[doc(hidden)]
			pub fn call_functions() -> #scrate::metadata_ir::PalletCallMetadataIR {
				#scrate::scale_info::meta_type::<Call<#type_use_gen>>().into()
			}
		}
	}
}
