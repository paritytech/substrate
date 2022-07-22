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
//! The #[define_env] attribute macro hides boilerplate of defining external environment
//! for a wasm module.
//!
//! Most likely you should use the `define_env` macro.

#![no_std]

extern crate alloc;

use alloc::{
	format,
	string::{String, ToString},
	vec::Vec,
};
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Ident};

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

/// Unparsed envirnoment definition.
struct EnvDefInput {
	item: syn::ItemMod,
	ident: syn::Ident,
}

/// Parsed envirnoment definition.
struct EnvDef {
	ident: syn::Ident,
	host_funcs: Vec<HostFn>,
}

/// Parsed host function definition.
struct HostFn {
	item: syn::ItemFn,
	module: String,
	name: String,
}

/// Helper trait to convert a host function definition into its wasm signature.
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
	pub fn try_from(item: syn::Item) -> syn::Result<Self> {
		let span = item.span();
		let err = || {
			let msg = "Invalid host function definition, only #[v(<u8>)] or #[unstable] attribute is allowed.";
			syn::Error::new(span, msg)
		};

		let item = match item {
			syn::Item::Fn(i_fn) => Ok(i_fn),
			_ => Err(err()),
		}?;

		let name = item.sig.ident.to_string();
		let mut module = "seal0".to_string();
		let attrs: Vec<&syn::Attribute> =
			item.attrs.iter().filter(|m| !m.path.is_ident("doc")).collect();

		match attrs.len() {
			0 => (),
			1 => {
				let attr = &attrs[0];
				let ident = attr.path.get_ident().ok_or(err())?.to_string();
				match ident.as_str() {
					"v" => {
						let ver: syn::LitInt = attr.parse_args()?;
						module = format!("seal{}", ver.base10_parse::<u8>().map_err(|_| err())?);
					},
					"unstable" => {
						module = "__unstable__".to_string();
					},
					_ => return Err(err()),
				}
			},
			_ => return Err(err()),
		}

		Ok(Self { item, module, name })
	}
}

impl EnvDef {
	pub fn try_from(input: EnvDefInput) -> syn::Result<Self> {
		let item = &input.item;
		let span = item.span();
		let err = |msg| syn::Error::new(span.clone(), msg);
		let items = &item
			.content
			.as_ref()
			.ok_or(
				err("Invalid environment definition, expected `mod` to be inlined.".to_string()),
			)?
			.1;

		let ident = input.ident;
		let mut host_funcs = Vec::<HostFn>::default();

		for i in items.iter() {
			host_funcs.push(HostFn::try_from(i.clone())?);
		}

		Ok(Self { ident, host_funcs })
	}
}

/// Expands environment definiton.
/// Should generate source code for:
///  - wasm import satisfy checks (see `expand_can_satisfy()`);
///  - implementations of the host functions to be added to the wasm runtime environment (see
///    `expand_impls()`).
fn expand_env(def: &mut EnvDef) -> proc_macro2::TokenStream {
	let can_satisfy = expand_can_satisfy(def);
	let impls = expand_impls(def);
	let env = &def.ident;

	quote! {
		pub struct #env;
		#can_satisfy
		#impls
	}
}

/// Generates `can_satisfy()` method for every host function, to be used to check
/// these functions versus expected module, name and signatures when imporing them from a wasm
/// module.
fn expand_can_satisfy(def: &mut EnvDef) -> proc_macro2::TokenStream {
	let checks = def.host_funcs.iter().map(|f| {
		let (module, name, signature) = (&f.module, &f.name, &f.to_wasm_sig());
		quote! {
			if module == #module.as_bytes()
				&& name == #name.as_bytes()
				&& signature == &#signature
			{
				return true;
			}
		}
	});
	let satisfy_checks = quote! {
		#( #checks )*
	};

	let env = &def.ident;
	quote! {
		impl crate::wasm::env_def::ImportSatisfyCheck for #env {
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

/// Generates implementation for every host function, to register it in the contract execution
/// environment.
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
						.expect(
							"precondition: all imports should be checked against the signatures of corresponding
							functions defined by `#[define_env]` proc macro by the user of the macro;
							thus this can never be `None`;
							qed;"
						);
					}
				} else { quote! { } }
			},
			_ => quote! { },
		}
	});

	let (outline, ret_ty) = match &f.item.sig.output {
		syn::ReturnType::Default => (
			quote! {
				body().map_err(|reason| {
					ctx.set_trap_reason(reason);
					sp_sandbox::HostError
				})?;
				return Ok(sp_sandbox::ReturnValue::Unit);
			},
			quote! {()}),
		syn::ReturnType::Type(_,ty) => (
			quote! {
				let r = body().map_err(|reason| {
						ctx.set_trap_reason(reason);
						sp_sandbox::HostError
					})?;
					return Ok(sp_sandbox::ReturnValue::Value({
						r.to_typed_value()
					}));
			},
			quote! {#ty}),
	};

	let params = params.clone();
	let (module, name, ident, body) = (&f.module, &f.name, &f.item.sig.ident, &f.item.block);
	let unstable_feat = match module.as_str() {
		"__unstable__" => quote! { #[cfg(feature = "unstable-interface")] },
		_ => quote! { },
	};
	quote! {
		#unstable_feat
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
				let body = crate::wasm::env_def::macros::constrain_closure::<#ret_ty, _>(|| {
					#( #params )*
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
	let env = &def.ident;

	quote! {
		impl<E: Ext> crate::wasm::env_def::FunctionImplProvider<E> for #env
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
	if attr.is_empty() {
		let msg = "Invalid `define_env` attribute macro: expected enviroment identificator, \
                         e.g. `#[define_env(Env)]`.";
		let span = proc_macro2::TokenStream::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into()
	}

	let item = syn::parse_macro_input!(item as syn::ItemMod);
	let ident = syn::parse_macro_input!(attr as syn::Ident);
	let input = EnvDefInput { item, ident };

	match EnvDef::try_from(input) {
		Ok(mut def) => expand_env(&mut def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
