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

use crate::construct_runtime::{Pallet, SYSTEM_PALLET_NAME};
use proc_macro2::TokenStream;
use quote::quote;
use std::str::FromStr;
use syn::{Generics, Ident};

pub fn expand_outer_origin(
	runtime: &Ident,
	system_pallet: &Pallet,
	pallets: &[Pallet],
	scrate: &TokenStream,
) -> syn::Result<TokenStream> {
	let mut caller_variants = TokenStream::new();
	let mut pallet_conversions = TokenStream::new();
	let mut query_origin_part_macros = Vec::new();

	for pallet_decl in pallets.iter().filter(|pallet| pallet.name != SYSTEM_PALLET_NAME) {
		if let Some(pallet_entry) = pallet_decl.find_part("Origin") {
			let instance = pallet_decl.instance.as_ref();
			let index = pallet_decl.index;
			let generics = &pallet_entry.generics;
			let name = &pallet_decl.name;
			let path = &pallet_decl.path;

			if instance.is_some() && generics.params.is_empty() {
				let msg = format!(
					"Instantiable pallet with no generic `Origin` cannot \
					 be constructed: pallet `{}` must have generic `Origin`",
					name
				);
				return Err(syn::Error::new(name.span(), msg))
			}

			caller_variants.extend(expand_origin_caller_variant(
				runtime,
				pallet_decl,
				index,
				instance,
				generics,
			));
			pallet_conversions.extend(expand_origin_pallet_conversions(
				scrate,
				runtime,
				pallet_decl,
				instance,
				generics,
			));
			query_origin_part_macros.push(quote! {
				#path::__substrate_origin_check::is_origin_part_defined!(#name);
			});
		}
	}

	let system_path = &system_pallet.path;

	let system_index = system_pallet.index;

	let system_path_name = system_path.module_name();

	let doc_string = get_intra_doc_string(
		"Origin is always created with the base filter configured in",
		&system_path_name,
	);

	let doc_string_none_origin =
		get_intra_doc_string("Create with system none origin and", &system_path_name);

	let doc_string_root_origin =
		get_intra_doc_string("Create with system root origin and", &system_path_name);

	let doc_string_signed_origin =
		get_intra_doc_string("Create with system signed origin and", &system_path_name);

	let doc_string_runtime_origin =
		get_intra_doc_string("Convert to runtime origin, using as filter:", &system_path_name);

	let doc_string_runtime_origin_with_caller = get_intra_doc_string(
		"Convert to runtime origin with caller being system signed or none and use filter",
		&system_path_name,
	);

	Ok(quote! {
		#( #query_origin_part_macros )*

		/// The runtime origin type representing the origin of a call.
		///
		#[doc = #doc_string]
		#[derive(Clone)]
		pub struct RuntimeOrigin {
			caller: OriginCaller,
			filter: #scrate::__private::sp_std::rc::Rc<Box<dyn Fn(&<#runtime as #system_path::Config>::RuntimeCall) -> bool>>,
		}

		#[cfg(not(feature = "std"))]
		impl #scrate::__private::sp_std::fmt::Debug for RuntimeOrigin {
			fn fmt(
				&self,
				fmt: &mut #scrate::__private::sp_std::fmt::Formatter,
			) -> #scrate::__private::sp_std::result::Result<(), #scrate::__private::sp_std::fmt::Error> {
				fmt.write_str("<wasm:stripped>")
			}
		}

		#[cfg(feature = "std")]
		impl #scrate::__private::sp_std::fmt::Debug for RuntimeOrigin {
			fn fmt(
				&self,
				fmt: &mut #scrate::__private::sp_std::fmt::Formatter,
			) -> #scrate::__private::sp_std::result::Result<(), #scrate::__private::sp_std::fmt::Error> {
				fmt.debug_struct("Origin")
					.field("caller", &self.caller)
					.field("filter", &"[function ptr]")
					.finish()
			}
		}

		impl #scrate::traits::OriginTrait for RuntimeOrigin {
			type Call = <#runtime as #system_path::Config>::RuntimeCall;
			type PalletsOrigin = OriginCaller;
			type AccountId = <#runtime as #system_path::Config>::AccountId;

			fn add_filter(&mut self, filter: impl Fn(&Self::Call) -> bool + 'static) {
				let f = self.filter.clone();

				self.filter = #scrate::__private::sp_std::rc::Rc::new(Box::new(move |call| {
					f(call) && filter(call)
				}));
			}

			fn reset_filter(&mut self) {
				let filter = <
					<#runtime as #system_path::Config>::BaseCallFilter
					as #scrate::traits::Contains<<#runtime as #system_path::Config>::RuntimeCall>
				>::contains;

				self.filter = #scrate::__private::sp_std::rc::Rc::new(Box::new(filter));
			}

			fn set_caller_from(&mut self, other: impl Into<Self>) {
				self.caller = other.into().caller;
			}

			fn filter_call(&self, call: &Self::Call) -> bool {
				match self.caller {
					// Root bypasses all filters
					OriginCaller::system(#system_path::Origin::<#runtime>::Root) => true,
					_ => (self.filter)(call),
				}
			}

			fn caller(&self) -> &Self::PalletsOrigin {
				&self.caller
			}

			fn into_caller(self) -> Self::PalletsOrigin {
				self.caller
			}

			fn try_with_caller<R>(
				mut self,
				f: impl FnOnce(Self::PalletsOrigin) -> Result<R, Self::PalletsOrigin>,
			) -> Result<R, Self> {
				match f(self.caller) {
					Ok(r) => Ok(r),
					Err(caller) => { self.caller = caller; Err(self) }
				}
			}

			fn none() -> Self {
				#system_path::RawOrigin::None.into()
			}

			fn root() -> Self {
				#system_path::RawOrigin::Root.into()
			}

			fn signed(by: Self::AccountId) -> Self {
				#system_path::RawOrigin::Signed(by).into()
			}
		}

		#[derive(
			Clone, PartialEq, Eq, #scrate::__private::RuntimeDebug, #scrate::__private::codec::Encode,
			#scrate::__private::codec::Decode, #scrate::__private::scale_info::TypeInfo, #scrate::__private::codec::MaxEncodedLen,
		)]
		#[allow(non_camel_case_types)]
		pub enum OriginCaller {
			#[codec(index = #system_index)]
			system(#system_path::Origin<#runtime>),
			#caller_variants
			#[allow(dead_code)]
			Void(#scrate::__private::Void)
		}

		// For backwards compatibility and ease of accessing these functions.
		#[allow(dead_code)]
		impl RuntimeOrigin {
			#[doc = #doc_string_none_origin]
			pub fn none() -> Self {
				<RuntimeOrigin as #scrate::traits::OriginTrait>::none()
			}

			#[doc = #doc_string_root_origin]
			pub fn root() -> Self {
				<RuntimeOrigin as #scrate::traits::OriginTrait>::root()
			}

			#[doc = #doc_string_signed_origin]
			pub fn signed(by: <#runtime as #system_path::Config>::AccountId) -> Self {
				<RuntimeOrigin as #scrate::traits::OriginTrait>::signed(by)
			}
		}

		impl From<#system_path::Origin<#runtime>> for OriginCaller {
			fn from(x: #system_path::Origin<#runtime>) -> Self {
				OriginCaller::system(x)
			}
		}

		impl #scrate::traits::CallerTrait<<#runtime as #system_path::Config>::AccountId> for OriginCaller {
			fn into_system(self) -> Option<#system_path::RawOrigin<<#runtime as #system_path::Config>::AccountId>> {
				match self {
					OriginCaller::system(x) => Some(x),
					_ => None,
				}
			}
			fn as_system_ref(&self) -> Option<&#system_path::RawOrigin<<#runtime as #system_path::Config>::AccountId>> {
				match &self {
					OriginCaller::system(o) => Some(o),
					_ => None,
				}
			}
		}

		impl TryFrom<OriginCaller> for #system_path::Origin<#runtime> {
			type Error = OriginCaller;
			fn try_from(x: OriginCaller)
				-> #scrate::__private::sp_std::result::Result<#system_path::Origin<#runtime>, OriginCaller>
			{
				if let OriginCaller::system(l) = x {
					Ok(l)
				} else {
					Err(x)
				}
			}
		}

		impl From<#system_path::Origin<#runtime>> for RuntimeOrigin {

			#[doc = #doc_string_runtime_origin]
			fn from(x: #system_path::Origin<#runtime>) -> Self {
				let o: OriginCaller = x.into();
				o.into()
			}
		}

		impl From<OriginCaller> for RuntimeOrigin {
			fn from(x: OriginCaller) -> Self {
				let mut o = RuntimeOrigin {
					caller: x,
					filter: #scrate::__private::sp_std::rc::Rc::new(Box::new(|_| true)),
				};

				#scrate::traits::OriginTrait::reset_filter(&mut o);

				o
			}
		}

		impl From<RuntimeOrigin> for #scrate::__private::sp_std::result::Result<#system_path::Origin<#runtime>, RuntimeOrigin> {
			/// NOTE: converting to pallet origin loses the origin filter information.
			fn from(val: RuntimeOrigin) -> Self {
				if let OriginCaller::system(l) = val.caller {
					Ok(l)
				} else {
					Err(val)
				}
			}
		}
		impl From<Option<<#runtime as #system_path::Config>::AccountId>> for RuntimeOrigin {
			#[doc = #doc_string_runtime_origin_with_caller]
			fn from(x: Option<<#runtime as #system_path::Config>::AccountId>) -> Self {
				<#system_path::Origin<#runtime>>::from(x).into()
			}
		}

		#pallet_conversions
	})
}

fn expand_origin_caller_variant(
	runtime: &Ident,
	pallet: &Pallet,
	index: u8,
	instance: Option<&Ident>,
	generics: &Generics,
) -> TokenStream {
	let part_is_generic = !generics.params.is_empty();
	let variant_name = &pallet.name;
	let path = &pallet.path;
	let attr = pallet.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
		let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
			.expect("was successfully parsed before; qed");
		quote! {
			#acc
			#attr
		}
	});

	match instance {
		Some(inst) if part_is_generic => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<#runtime, #path::#inst>),
		},
		Some(inst) => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<#path::#inst>),
		},
		None if part_is_generic => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<#runtime>),
		},
		None => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin),
		},
	}
}

fn expand_origin_pallet_conversions(
	scrate: &TokenStream,
	runtime: &Ident,
	pallet: &Pallet,
	instance: Option<&Ident>,
	generics: &Generics,
) -> TokenStream {
	let path = &pallet.path;
	let variant_name = &pallet.name;

	let part_is_generic = !generics.params.is_empty();
	let pallet_origin = match instance {
		Some(inst) if part_is_generic => quote!(#path::Origin<#runtime, #path::#inst>),
		Some(inst) => quote!(#path::Origin<#path::#inst>),
		None if part_is_generic => quote!(#path::Origin<#runtime>),
		None => quote!(#path::Origin),
	};

	let doc_string = get_intra_doc_string(" Convert to runtime origin using", &path.module_name());
	let attr = pallet.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
		let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
			.expect("was successfully parsed before; qed");
		quote! {
			#acc
			#attr
		}
	});

	quote! {
		#attr
		impl From<#pallet_origin> for OriginCaller {
			fn from(x: #pallet_origin) -> Self {
				OriginCaller::#variant_name(x)
			}
		}

		#attr
		impl From<#pallet_origin> for RuntimeOrigin {
			#[doc = #doc_string]
			fn from(x: #pallet_origin) -> Self {
				let x: OriginCaller = x.into();
				x.into()
			}
		}

		#attr
		impl From<RuntimeOrigin> for #scrate::__private::sp_std::result::Result<#pallet_origin, RuntimeOrigin> {
			/// NOTE: converting to pallet origin loses the origin filter information.
			fn from(val: RuntimeOrigin) -> Self {
				if let OriginCaller::#variant_name(l) = val.caller {
					Ok(l)
				} else {
					Err(val)
				}
			}
		}

		#attr
		impl TryFrom<OriginCaller> for #pallet_origin {
			type Error = OriginCaller;
			fn try_from(
				x: OriginCaller,
			) -> #scrate::__private::sp_std::result::Result<#pallet_origin, OriginCaller> {
				if let OriginCaller::#variant_name(l) = x {
					Ok(l)
				} else {
					Err(x)
				}
			}
		}

		#attr
		impl<'a> TryFrom<&'a OriginCaller> for &'a #pallet_origin {
			type Error = ();
			fn try_from(
				x: &'a OriginCaller,
			) -> #scrate::__private::sp_std::result::Result<&'a #pallet_origin, ()> {
				if let OriginCaller::#variant_name(l) = x {
					Ok(&l)
				} else {
					Err(())
				}
			}
		}

		#attr
		impl<'a> TryFrom<&'a RuntimeOrigin> for &'a #pallet_origin {
			type Error = ();
			fn try_from(
				x: &'a RuntimeOrigin,
			) -> #scrate::__private::sp_std::result::Result<&'a #pallet_origin, ()> {
				if let OriginCaller::#variant_name(l) = &x.caller {
					Ok(&l)
				} else {
					Err(())
				}
			}
		}
	}
}

// Get the actual documentation using the doc information and system path name
fn get_intra_doc_string(doc_info: &str, system_path_name: &String) -> String {
	format!(" {} [`{}::Config::BaseCallFilter`].", doc_info, system_path_name)
}
