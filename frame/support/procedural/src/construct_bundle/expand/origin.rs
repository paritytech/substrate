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

use crate::construct_bundle::{Pallet, SYSTEM_PALLET_NAME};
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

			// caller_variants.extend(expand_origin_caller_variant(
			// 	runtime,
			// 	pallet_decl,
			// 	index,
			// 	instance,
			// 	generics,
			// ));
			// pallet_conversions.extend(expand_origin_pallet_conversions(
			// 	scrate,
			// 	runtime,
			// 	pallet_decl,
			// 	instance,
			// 	generics,
			// ));
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
		// #( #query_origin_part_macros )*

		/// The runtime origin type representing the origin of a call.
		///
		#[doc = #doc_string]
		#[derive(Clone, Eq, PartialEq, #scrate::codec::Encode,
			#scrate::codec::Decode, #scrate::scale_info::TypeInfo, #scrate::codec::MaxEncodedLen)]
		pub struct Origin<T: Config> {
			caller: OriginCaller<T>,
			// filter: #scrate::sp_std::rc::Rc<Box<dyn Fn(&Call<T>) -> bool>>,
		}

		// #[cfg(not(feature = "std"))]
		// impl<T: Config> #scrate::sp_std::fmt::Debug for Origin<T> {
		// 	fn fmt(
		// 		&self,
		// 		fmt: &mut #scrate::sp_std::fmt::Formatter,
		// 	) -> #scrate::sp_std::result::Result<(), #scrate::sp_std::fmt::Error> {
		// 		fmt.write_str("<wasm:stripped>")
		// 	}
		// }

		// #[cfg(feature = "std")]
		// impl<T: Config> #scrate::sp_std::fmt::Debug for Origin<T> {
		// 	fn fmt(
		// 		&self,
		// 		fmt: &mut #scrate::sp_std::fmt::Formatter,
		// 	) -> #scrate::sp_std::result::Result<(), #scrate::sp_std::fmt::Error> {
		// 		fmt.debug_struct("Origin")
		// 			.field("caller", &self.caller)
		// 			.field("filter", &"[function ptr]")
		// 			.finish()
		// 	}
		// }

		impl<T: Config> #scrate::traits::OriginTrait for Origin<T> {
			type Call = Call<T>; //<#runtime as #system_path::Config>::RuntimeCall;
			type PalletsOrigin = OriginCaller<T>;
			type AccountId = <T as #system_path::Config>::AccountId;

			fn add_filter(&mut self, filter: impl Fn(&Self::Call) -> bool + 'static) {
				// let f = self.filter.clone();

				// self.filter = #scrate::sp_std::rc::Rc::new(Box::new(move |call| {
				// 	f(call) && filter(call)
				// }));
			}

			fn reset_filter(&mut self) {
				// let filter = <
				// 	<T as Config>::BaseCallFilter
				// 	as #scrate::traits::Contains<Call<T>>
				// >::contains;

				// self.filter = #scrate::sp_std::rc::Rc::new(Box::new(filter));
			}

			fn set_caller_from(&mut self, other: impl Into<Self>) {
				// self.caller = other.into().caller;
			}

			fn filter_call(&self, call: &Self::Call) -> bool {
				// match self.caller {
				// 	// Root bypasses all filters
				// 	OriginCaller::<T>::system(#system_path::Origin::<T>::Root) => true,
				// 	_ => (self.filter)(call),
				// }
				true
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
				// match f(self.caller) {
				// 	Ok(r) => Ok(r),
				// 	Err(caller) => { self.caller = caller; Err(self) }
				// }
				Err(self)
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
			Clone, PartialEq, Eq, #scrate::RuntimeDebug, #scrate::codec::Encode,
			#scrate::codec::Decode, #scrate::scale_info::TypeInfo, #scrate::codec::MaxEncodedLen,
		)]
		#[allow(non_camel_case_types)]
		pub enum OriginCaller<T: Config> {
			#[codec(index = #system_index)]
			system(#system_path::Origin<T>),
			#caller_variants
			#[allow(dead_code)]
			Void(#scrate::Void)
		}

		// // For backwards compatibility and ease of accessing these functions.
		// #[allow(dead_code)]
		// impl<T: Config> Origin<T> {
		// 	#[doc = #doc_string_none_origin]
		// 	pub fn none() -> Self {
		// 		<Origin<T> as #scrate::traits::OriginTrait>::none()
		// 	}

		// 	#[doc = #doc_string_root_origin]
		// 	pub fn root() -> Self {
		// 		<Origin<T> as #scrate::traits::OriginTrait>::root()
		// 	}

		// 	#[doc = #doc_string_signed_origin]
		// 	pub fn signed(by: <T as #system_path::Config>::AccountId) -> Self {
		// 		<Origin<T> as #scrate::traits::OriginTrait>::signed(by)
		// 	}
		// }

		impl<T: Config> From<#system_path::Origin<T>> for OriginCaller<T> {
			fn from(x: #system_path::Origin<T>) -> Self {
				// OriginCaller::<T>::system(x)
				unreachable!()
			}
		}

		impl<T: Config> #scrate::traits::CallerTrait<<T as #system_path::Config>::AccountId> for OriginCaller<T> {
			fn into_system(self) -> Option<#system_path::RawOrigin<<T as #system_path::Config>::AccountId>> {
				// match self {
				// 	OriginCaller::<T>::system(x) => Some(x),
				// 	_ => None,
				// }
				None
			}
			fn as_system_ref(&self) -> Option<&#system_path::RawOrigin<<T as #system_path::Config>::AccountId>> {
				// match &self {
				// 	OriginCaller::<T>::system(o) => Some(o),
				// 	_ => None,
				// }
				None
			}
		}

		impl<T: Config> TryFrom<OriginCaller<T>> for #system_path::Origin<T> {
			type Error = OriginCaller<T>;
			fn try_from(x: OriginCaller<T>)
				-> #scrate::sp_std::result::Result<#system_path::Origin<T>, OriginCaller<T>>
			{
				// if let OriginCaller::<T>::system(l) = x {
				// 	Ok(l)
				// } else {
				// 	Err(x)
				// }
				Err(x)
			}
		}

		impl<T: Config> From<#system_path::Origin<T>> for Origin<T> {

			#[doc = #doc_string_runtime_origin]
			fn from(x: #system_path::Origin<T>) -> Self {
				// let o: OriginCaller<T> = x.into();
				// o.into()
				unreachable!()
			}
		}

		impl<T: Config> From<OriginCaller<T>> for Origin<T> {
			fn from(x: OriginCaller<T>) -> Self {
				// let mut o = Origin<T> {
				// 	caller: x,
				// 	// filter: #scrate::sp_std::rc::Rc::new(Box::new(|_| true)),
				// };

				// // #scrate::traits::OriginTrait::reset_filter(&mut o);

				// o
				unreachable!()
			}
		}

		impl<T: Config> From<Origin<T>> for #scrate::sp_std::result::Result<#system_path::Origin<T>, Origin<T>> {
			/// NOTE: converting to pallet origin loses the origin filter information.
			fn from(val: Origin<T>) -> Self {
				// if let OriginCaller::<T>::system(l) = val.caller {
				// 	Ok(l)
				// } else {
				// 	Err(val)
				// }
				Err(val)
			}
		}

		impl<T: Config> From<Option<<T as #system_path::Config>::AccountId>> for Origin<T> {
			#[doc = #doc_string_runtime_origin_with_caller]
			fn from(x: Option<<T as #system_path::Config>::AccountId>) -> Self {
				// #system_path::Origin::<T>::from(x).into()
				unreachable!()
			}
		}

		#pallet_conversions
	})
}

/* 
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
			#variant_name(#path::Origin<T, #path::#inst>),
		},
		Some(inst) => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<T, #path::#inst>),
		},
		None if part_is_generic => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<T>),
		},
		None => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::Origin<T>),
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
		Some(inst) if part_is_generic => quote!(#path::Origin<T, #path::#inst>),
		Some(inst) => quote!(#path::Origin<T, #path::#inst>),
		None if part_is_generic => quote!(#path::Origin<T>),
		None => quote!(#path::Origin<T>),
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
		impl<T> From<#pallet_origin> for OriginCaller<T> {
			fn from(x: #pallet_origin) -> Self {
				OriginCaller::<T>::#variant_name(x)
			}
		}

		#attr
		impl<T> From<#pallet_origin> for Origin<T> {
			#[doc = #doc_string]
			fn from(x: #pallet_origin) -> Self {
				let x: OriginCaller<T> = x.into();
				x.into()
			}
		}

		#attr
		impl<T> From<Origin<T>> for #scrate::sp_std::result::Result<#pallet_origin, Origin<T>> {
			/// NOTE: converting to pallet origin loses the origin filter information.
			fn from(val: Origin<T>) -> Self {
				if let OriginCaller::<T>::#variant_name(l) = val.caller {
					Ok(l)
				} else {
					Err(val)
				}
			}
		}

		#attr
		impl<T> TryFrom<OriginCaller<T>> for #pallet_origin {
			type Error = OriginCaller<T>;
			fn try_from(
				x: OriginCaller<T>,
			) -> #scrate::sp_std::result::Result<#pallet_origin, OriginCaller<T>> {
				if let OriginCaller::<T>::#variant_name(l) = x {
					Ok(l)
				} else {
					Err(x)
				}
			}
		}

		#attr
		impl<T, 'a> TryFrom<&'a OriginCaller<T>> for &'a #pallet_origin {
			type Error = ();
			fn try_from(
				x: &'a OriginCaller<T>,
			) -> #scrate::sp_std::result::Result<&'a #pallet_origin, ()> {
				if let OriginCaller::<T>::#variant_name(l) = x {
					Ok(&l)
				} else {
					Err(())
				}
			}
		}

		#attr
		impl<T, 'a> TryFrom<&'a Origin<T>> for &'a #pallet_origin {
			type Error = ();
			fn try_from(
				x: &'a Origin<T>,
			) -> #scrate::sp_std::result::Result<&'a #pallet_origin, ()> {
				if let OriginCaller::<T>::#variant_name(l) = &x.caller {
					Ok(&l)
				} else {
					Err(())
				}
			}
		}
	}
}
*/

// Get the actual documentation using the doc information and system path name
fn get_intra_doc_string(doc_info: &str, system_path_name: &String) -> String {
	format!(" {} [`{}::Config::BaseCallFilter`].", doc_info, system_path_name)
}
