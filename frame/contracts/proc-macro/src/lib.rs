// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Proc macros used in the contracts module.

#![no_std]

extern crate alloc;

use alloc::{
	boxed::Box,
	string::{String, ToString},
	vec,
	vec::Vec,
};
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Ident, Item, ItemFn};

/// This derives `Debug` for a struct where each field must be of some numeric type.
/// It interprets each field as its represents some weight and formats it as times so that
/// it is readable by humans.
#[proc_macro_derive(WeightDebug)]
pub fn derive_weight_debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	derive_debug(input, format_weight)
}

/// This is basically identical to the std libs Debug derive but without adding any
/// bounds to existing generics.
#[proc_macro_derive(ScheduleDebug)]
pub fn derive_schedule_debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	derive_debug(input, format_default)
}

fn derive_debug(
	input: proc_macro::TokenStream,
	fmt: impl Fn(&Ident) -> TokenStream,
) -> proc_macro::TokenStream {
	let input = parse_macro_input!(input as DeriveInput);
	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	let data = if let Data::Struct(data) = &input.data {
		data
	} else {
		return quote_spanned! {
			name.span() =>
			compile_error!("WeightDebug is only supported for structs.");
		}
		.into()
	};

	#[cfg(feature = "full")]
	let fields = iterate_fields(data, fmt);

	#[cfg(not(feature = "full"))]
	let fields = {
		drop(fmt);
		drop(data);
		TokenStream::new()
	};

	let tokens = quote! {
		impl #impl_generics core::fmt::Debug for #name #ty_generics #where_clause {
			fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
				use ::sp_runtime::{FixedPointNumber, FixedU128 as Fixed};
				let mut formatter = formatter.debug_struct(stringify!(#name));
				#fields
				formatter.finish()
			}
		}
	};

	tokens.into()
}

/// This is only used then the `full` feature is activated.
#[cfg(feature = "full")]
fn iterate_fields(data: &syn::DataStruct, fmt: impl Fn(&Ident) -> TokenStream) -> TokenStream {
	use syn::Fields;

	match &data.fields {
		Fields::Named(fields) => {
			let recurse = fields.named.iter().filter_map(|f| {
				let name = f.ident.as_ref()?;
				if name.to_string().starts_with('_') {
					return None
				}
				let value = fmt(name);
				let ret = quote_spanned! { f.span() =>
					formatter.field(stringify!(#name), #value);
				};
				Some(ret)
			});
			quote! {
				#( #recurse )*
			}
		},
		Fields::Unnamed(fields) => quote_spanned! {
			fields.span() =>
			compile_error!("Unnamed fields are not supported")
		},
		Fields::Unit => quote!(),
	}
}

fn format_weight(field: &Ident) -> TokenStream {
	quote_spanned! { field.span() =>
		&if self.#field > 1_000_000_000 {
			format!(
				"{:.1?} ms",
				Fixed::saturating_from_rational(self.#field, 1_000_000_000).to_float()
			)
		} else if self.#field > 1_000_000 {
			format!(
				"{:.1?} µs",
				Fixed::saturating_from_rational(self.#field, 1_000_000).to_float()
			)
		} else if self.#field > 1_000 {
			format!(
				"{:.1?} ns",
				Fixed::saturating_from_rational(self.#field, 1_000).to_float()
			)
		} else {
			format!("{} ps", self.#field)
		}
	}
}

fn format_default(field: &Ident) -> TokenStream {
	quote_spanned! { field.span() =>
		&self.#field
	}
}

// define_env! macro re-write
// first we parse env mod
// then we expand, i.e.
// should generate code for:
// 1. can_satisfy checks: #can_satisfy
//    expand def, so just add parts related to the new func to it, and return updated def as a token
// stream    see how it's done in pallet proc macro, e.g. in constants
// 2. impls() for the set of host functions: #impls

/// parsed definition of env
/// (inspired by pallet attribute macro, see /frame/support/procedural/src/pallet/)
struct EnvDef {
	pub item: syn::ItemMod,      // the whole env module
	pub host_funcs: Vec<HostFn>, // set of host fuctions
}

struct HostFn {
	item: syn::ItemFn,
	module: String,
	name: String,
}

trait ToWasmSig {
	fn to_wasm_sig(&self) -> TokenStream;
}

impl ToWasmSig for HostFn {
	fn to_wasm_sig(&self) -> TokenStream {
		let args = self.item.sig.inputs.iter().skip(1).filter_map(|a| match a {
			syn::FnArg::Typed(pt) => Some(&pt.ty),
			_ => None,
		});

		let returns = match &self.item.sig.output {
			syn::ReturnType::Type(_, bt) => quote! { vec![ #bt::VALUE_TYPE ] },
			_ => quote! { vec![] },
		};

		quote! {
			 wasm_instrument::parity_wasm::elements::FunctionType::new(
				vec! [ #(<#args>::VALUE_TYPE),* ],
				#returns,
			)
		}
	}
}

impl ToTokens for HostFn {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.item.to_tokens(tokens);
	}
}

impl HostFn {
	pub fn try_from(mut item: syn::Item) -> syn::Result<Self> {
		let span = item.span();
		let err = || {
			let msg = "Invalid environment definition, only fn with #[host(\"...\")] attribute are allowed.";
			syn::Error::new(span, msg)
		};

		let mut item = match item {
			syn::Item::Fn(i_fn) => Ok(i_fn),
			_ => Err(err()),
		}?;

		let attr = item.attrs.pop().ok_or(err())?;
		let module = attr.parse_args().map(|a: syn::LitStr| a.value())?;
		let name = item.sig.ident.to_string();
		attr.path
			.get_ident()
			.ok_or(err())?
			.to_string()
			.eq("host")
			.then(|| Ok(Self { item, module, name }))
			.ok_or(err())?
	}
}

impl EnvDef {
	pub fn try_from(mut item: syn::ItemMod) -> syn::Result<Self> {
		let item_span = item.span();
		let items = &mut item
			.content
			.as_mut()
			.ok_or_else(|| {
				let msg = "Invalid environment definition, expected mod to be inlined.";
				syn::Error::new(item_span, msg)
			})?
			.1;
		let mut host_funcs = Vec::<HostFn>::default();

		for i in items.iter() {
			host_funcs.push(HostFn::try_from(i.clone())?);
		}

		Ok(Self { item, host_funcs })
	}
}

fn expand_env(def: &mut EnvDef) -> proc_macro2::TokenStream {
	// should generate code for:
	// 1. can_satisfy checks: #can_satisfy
	//    expand def, so just add parts related to the new func to it, and return updated def as a
	// token stream    see how it's done in pallet proc macro, e.g. in constants
	// 2. impls() for the set of host functions: #impls
	let can_satisfy = expand_can_satisfy(def);
	let impls = expand_impls(def);
	quote! {
		pub struct Env;
		#can_satisfy
		#impls
	}
}

// Adds check to can_satisfy for a new host fn
fn expand_can_satisfy(def: &mut EnvDef) -> proc_macro2::TokenStream {
	let checks = def.host_funcs.iter().map(|f| {
		let (module, name, signature) = (&f.module, &f.name, &f.to_wasm_sig());
		quote! {
			if module == #module.as_bytes()
				&& name == #name.as_bytes()
				&& signature == #signature
			{
				return true;
			}
		}
	});

	let satisfy_checks = quote! {
		#( #checks )*
	};

	quote! {
		impl crate::wasm::env_def::ImportSatisfyCheck for Env {
			fn can_satisfy(
					module: &[u8],
					name: &[u8],
					signature: &wasm_instrument::parity_wasm::elements::FunctionType,
				) -> bool {
					use crate::wasm::env_def::ConvertibleToWasm;
					#[cfg(not(feature = "unstable-interface"))]
					if module == b"__unstable__" {
						return false;
					}
					#satisfy_checks
					return false;
				}
		}
	}
}

fn expand_impls(def: &mut EnvDef) -> proc_macro2::TokenStream {
	let impls =  def.host_funcs.iter().map(|f| {
	let params = &f.item.sig.inputs.iter().skip(1).map(|arg| {
	       match arg {
		syn::FnArg::Typed(pt) => {
		    if let syn::Pat::Ident(ident) = &*pt.pat {
			let p_type = &pt.ty;
			let p_name = ident.ident.clone();
			quote! {
			    let #p_name : <#p_type as crate::wasm::env_def::ConvertibleToWasm>::NativeType =
				    args.next()
				    .and_then(|v| <#p_type as crate::wasm::env_def::ConvertibleToWasm>::from_typed_value(v.clone()))
				    // TBD: update this msg
				    .expect(
						    "precondition: all imports should be checked against the signatures of corresponding
						    functions defined by `#[define_env]` proc macro by the user of the macro;
						    signatures of these functions defined by `$params`;
						    calls always made with arguments types of which are defined by the corresponding imports;
						    thus types of arguments should be equal to type list in `$params` and
						    length of argument list and $params should be equal;
						    thus this can never be `None`;
						    qed;
						    "
				    );
			}
		    } else { quote! { } }
		},
		_ => quote! { }}
	});

	let outline = match &f.item.sig.output {
	   syn::ReturnType::Default => quote! {
					      body().map_err(|reason| {
							      ctx.set_trap_reason(reason);
							      sp_sandbox::HostError
							  })?;
					      return Ok(sp_sandbox::ReturnValue::Unit);
					   },
	    syn::ReturnType::Type(_,_) => quote! {
					      let r = body().map_err(|reason| {
					                     ctx.set_trap_reason(reason);
			  				     sp_sandbox::HostError
							 })?;
							 return Ok(sp_sandbox::ReturnValue::Value({
							     use crate::wasm::env_def::ConvertibleToWasm;
							     r.to_typed_value()
							 }));
	    	    	    	    	    },
	};

	let p = params.clone();
	let (module, name, ident, body) = (&f.module, &f.name, &f.item.sig.ident, &f.item.block);
	quote! {
	      f(#module.as_bytes(), #name.as_bytes(), {
                fn #ident<E: Ext>(
                    ctx: &mut crate::wasm::Runtime<E>,
                    args: &[sp_sandbox::Value],
                ) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError>
                where
                    <E::T as frame_system::Config>::AccountId: sp_core::crypto::UncheckedFrom<<E::T as frame_system::Config>::Hash>
                        + AsRef<[u8]>,
                {
                    #[allow(unused)]
                    let mut args = args.iter();
		      let body = crate::wasm::env_def::macros::constrain_closure::<(), _>(|| {
			  #( #p )*
			  #body
		      });
		    #outline
		}
		#ident::<E>
	      });
	}
    });
	let packed_impls = quote! {
	#( #impls )*
	};
	quote! {
		impl<E: Ext> crate::wasm::env_def::FunctionImplProvider<E> for Env
		where
			<E::T as frame_system::Config>::AccountId:
			sp_core::crypto::UncheckedFrom<<E::T as frame_system::Config>::Hash> + AsRef<[u8]>,
		{
			fn impls<F: FnMut(&[u8], &[u8], crate::wasm::env_def::HostFunc<E>)>(f: &mut F) {
				#packed_impls
			}
		}
	}
}

#[proc_macro_attribute]
pub fn define_env(
	attr: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	if !attr.is_empty() {
		let msg = "Invalid define_env macro call: expected no attributes, the call must be just \
			`#[define_env]`";
		let span = proc_macro2::TokenStream::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into()
	}

	let i = syn::parse_macro_input!(item as syn::ItemMod);
	match EnvDef::try_from(i) {
		Ok(mut def) => expand_env(&mut def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
