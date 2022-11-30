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

//! Procedural macroses used in the contracts module.
//!
//! Most likely you should use the [`#[define_env]`][`macro@define_env`] attribute macro which hides
//! boilerplate of defining external environment for a wasm module.

#![no_std]

extern crate alloc;

use alloc::{
	format,
	string::{String, ToString},
	vec::Vec,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, FnArg, Ident};

/// This derives `Debug` for a struct where each field must be of some numeric type.
/// It interprets each field as its represents some weight and formats it as times so that
/// it is readable by humans.
#[proc_macro_derive(WeightDebug)]
pub fn derive_weight_debug(input: TokenStream) -> TokenStream {
	derive_debug(input, format_weight)
}

/// This is basically identical to the std libs Debug derive but without adding any
/// bounds to existing generics.
#[proc_macro_derive(ScheduleDebug)]
pub fn derive_schedule_debug(input: TokenStream) -> TokenStream {
	derive_debug(input, format_default)
}

fn derive_debug(input: TokenStream, fmt: impl Fn(&Ident) -> TokenStream2) -> TokenStream {
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
		TokenStream2::new()
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
fn iterate_fields(data: &syn::DataStruct, fmt: impl Fn(&Ident) -> TokenStream2) -> TokenStream2 {
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

fn format_weight(field: &Ident) -> TokenStream2 {
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

fn format_default(field: &Ident) -> TokenStream2 {
	quote_spanned! { field.span() =>
		&self.#field
	}
}

/// Parsed environment definition.
struct EnvDef {
	host_funcs: Vec<HostFn>,
}

/// Parsed host function definition.
struct HostFn {
	item: syn::ItemFn,
	module: String,
	name: String,
	returns: HostFnReturn,
	is_stable: bool,
}

enum HostFnReturn {
	Unit,
	U32,
	ReturnCode,
}

impl HostFnReturn {
	fn to_wasm_sig(&self) -> TokenStream2 {
		let ok = match self {
			Self::Unit => quote! { () },
			Self::U32 | Self::ReturnCode => quote! { ::core::primitive::u32 },
		};
		quote! {
			::core::result::Result<#ok, ::wasmi::core::Trap>
		}
	}
}

impl ToTokens for HostFn {
	fn to_tokens(&self, tokens: &mut TokenStream2) {
		self.item.to_tokens(tokens);
	}
}

impl HostFn {
	pub fn try_from(item: syn::ItemFn) -> syn::Result<Self> {
		let err = |span, msg| {
			let msg = format!("Invalid host function definition. {}", msg);
			syn::Error::new(span, msg)
		};

		// process attributes
		let msg =
			"only #[version(<u8>)], #[unstable] and #[prefixed_alias] attributes are allowed.";
		let span = item.span();
		let mut attrs = item.attrs.clone();
		attrs.retain(|a| !(a.path.is_ident("doc") || a.path.is_ident("prefixed_alias")));
		let name = item.sig.ident.to_string();
		let mut maybe_module = None;
		let mut is_stable = true;
		while let Some(attr) = attrs.pop() {
			let ident = attr.path.get_ident().ok_or(err(span, msg))?.to_string();
			match ident.as_str() {
				"version" => {
					if maybe_module.is_some() {
						return Err(err(span, "#[version] can only be specified once"))
					}
					let ver: u8 =
						attr.parse_args::<syn::LitInt>().and_then(|lit| lit.base10_parse())?;
					maybe_module = Some(format!("seal{}", ver));
				},
				"unstable" => {
					if !is_stable {
						return Err(err(span, "#[unstable] can only be specified once"))
					}
					is_stable = false;
				},
				_ => return Err(err(span, msg)),
			}
		}

		// process arguments: The first and second arg are treated differently (ctx, memory)
		// they must exist and be `ctx: _` and `memory: _`.
		let msg = "Every function must start with two inferred parameters: ctx: _ and memory: _";
		let special_args = item
			.sig
			.inputs
			.iter()
			.take(2)
			.enumerate()
			.map(|(i, arg)| is_valid_special_arg(i, arg))
			.fold(0u32, |acc, valid| if valid { acc + 1 } else { acc });

		if special_args != 2 {
			return Err(err(span, msg))
		}

		// process return type
		let msg = r#"Should return one of the following:
				- Result<(), TrapReason>,
				- Result<ReturnCode, TrapReason>,
				- Result<u32, TrapReason>"#;
		let ret_ty = match item.clone().sig.output {
			syn::ReturnType::Type(_, ty) => Ok(ty.clone()),
			_ => Err(err(span, &msg)),
		}?;
		match *ret_ty {
			syn::Type::Path(tp) => {
				let result = &tp.path.segments.last().ok_or(err(span, &msg))?;
				let (id, span) = (result.ident.to_string(), result.ident.span());
				id.eq(&"Result".to_string()).then_some(()).ok_or(err(span, &msg))?;

				match &result.arguments {
					syn::PathArguments::AngleBracketed(group) => {
						if group.args.len() != 2 {
							return Err(err(span, &msg))
						};

						let arg2 = group.args.last().ok_or(err(span, &msg))?;

						let err_ty = match arg2 {
							syn::GenericArgument::Type(ty) => Ok(ty.clone()),
							_ => Err(err(arg2.span(), &msg)),
						}?;

						match err_ty {
							syn::Type::Path(tp) => Ok(tp
								.path
								.segments
								.first()
								.ok_or(err(arg2.span(), &msg))?
								.ident
								.to_string()),
							_ => Err(err(tp.span(), &msg)),
						}?
						.eq("TrapReason")
						.then_some(())
						.ok_or(err(span, &msg))?;

						let arg1 = group.args.first().ok_or(err(span, &msg))?;
						let ok_ty = match arg1 {
							syn::GenericArgument::Type(ty) => Ok(ty.clone()),
							_ => Err(err(arg1.span(), &msg)),
						}?;
						let ok_ty_str = match ok_ty {
							syn::Type::Path(tp) => Ok(tp
								.path
								.segments
								.first()
								.ok_or(err(arg1.span(), &msg))?
								.ident
								.to_string()),
							syn::Type::Tuple(tt) => {
								if !tt.elems.is_empty() {
									return Err(err(arg1.span(), &msg))
								};
								Ok("()".to_string())
							},
							_ => Err(err(ok_ty.span(), &msg)),
						}?;
						let returns = match ok_ty_str.as_str() {
							"()" => Ok(HostFnReturn::Unit),
							"u32" => Ok(HostFnReturn::U32),
							"ReturnCode" => Ok(HostFnReturn::ReturnCode),
							_ => Err(err(arg1.span(), &msg)),
						}?;

						Ok(Self {
							item,
							module: maybe_module.unwrap_or_else(|| "seal0".to_string()),
							name,
							returns,
							is_stable,
						})
					},
					_ => Err(err(span, &msg)),
				}
			},
			_ => Err(err(span, &msg)),
		}
	}
}

impl EnvDef {
	pub fn try_from(item: syn::ItemMod) -> syn::Result<Self> {
		let span = item.span();
		let err = |msg| syn::Error::new(span, msg);
		let items = &item
			.content
			.as_ref()
			.ok_or(err("Invalid environment definition, expected `mod` to be inlined."))?
			.1;

		let extract_fn = |i: &syn::Item| match i {
			syn::Item::Fn(i_fn) => Some(i_fn.clone()),
			_ => None,
		};

		let selector = |a: &syn::Attribute| a.path.is_ident("prefixed_alias");

		let aliases = items
			.iter()
			.filter_map(extract_fn)
			.filter(|i| i.attrs.iter().any(selector))
			.map(|mut i| {
				i.attrs.retain(|i| !selector(i));
				i.sig.ident = syn::Ident::new(
					&format!("seal_{}", &i.sig.ident.to_string()),
					i.sig.ident.span(),
				);
				i
			})
			.map(|i| HostFn::try_from(i));

		let host_funcs = items
			.iter()
			.filter_map(extract_fn)
			.map(|i| HostFn::try_from(i))
			.chain(aliases)
			.collect::<Result<Vec<_>, _>>()?;

		Ok(Self { host_funcs })
	}
}

fn is_valid_special_arg(idx: usize, arg: &FnArg) -> bool {
	let pat = if let FnArg::Typed(pat) = arg { pat } else { return false };
	let ident = if let syn::Pat::Ident(ref ident) = *pat.pat { &ident.ident } else { return false };
	let name_ok = match idx {
		0 => ident == "ctx" || ident == "_ctx",
		1 => ident == "memory" || ident == "_memory",
		_ => false,
	};
	if !name_ok {
		return false
	}
	matches!(*pat.ty, syn::Type::Infer(_))
}

/// Expands environment definiton.
/// Should generate source code for:
///  - implementations of the host functions to be added to the wasm runtime environment (see
///    `expand_impls()`).
fn expand_env(def: &mut EnvDef) -> TokenStream2 {
	let impls = expand_impls(def);

	quote! {
		pub struct Env;
		#impls
	}
}

/// Generates for every host function:
///   - real implementation, to register it in the contract execution environment;
///   - dummy implementation, to be used as mocks for contract validation step.
fn expand_impls(def: &mut EnvDef) -> TokenStream2 {
	let impls = expand_functions(def, true, quote! { crate::wasm::Runtime<E> });
	let dummy_impls = expand_functions(def, false, quote! { () });

	quote! {
		impl<'a, E> crate::wasm::Environment<crate::wasm::runtime::Runtime<'a, E>> for Env
		where
			E: Ext,
			<E::T as ::frame_system::Config>::AccountId:
				::sp_core::crypto::UncheckedFrom<<E::T as ::frame_system::Config>::Hash> + ::core::convert::AsRef<[::core::primitive::u8]>,
		{
			fn define(store: &mut ::wasmi::Store<crate::wasm::Runtime<E>>, linker: &mut ::wasmi::Linker<crate::wasm::Runtime<E>>, allow_unstable: bool) -> Result<(), ::wasmi::errors::LinkerError> {
				#impls
				Ok(())
			}
		}

		impl crate::wasm::Environment<()> for Env
		{
			fn define(store: &mut ::wasmi::Store<()>, linker: &mut ::wasmi::Linker<()>, allow_unstable: bool) -> Result<(), ::wasmi::errors::LinkerError> {
				#dummy_impls
				Ok(())
			}
		}
	}
}

fn expand_functions(
	def: &mut EnvDef,
	expand_blocks: bool,
	host_state: TokenStream2,
) -> TokenStream2 {
	let impls = def.host_funcs.iter().map(|f| {
		// skip the context and memory argument
		let params = f.item.sig.inputs.iter().skip(2);
		let (module, name, body, wasm_output, output) = (
			&f.module,
			&f.name,
			&f.item.block,
			f.returns.to_wasm_sig(),
			&f.item.sig.output
		);
		let is_stable = f.is_stable;

		// If we don't expand blocks (implementing for `()`) we change a few things:
		// - We replace any code by unreachable!
		// - Allow unused variables as the code that uses is not expanded
		// - We don't need to map the error as we simply panic if they code would ever be executed
		let inner = if expand_blocks {
			quote! { || #output {
				let (memory, ctx) = __caller__
					.host_data()
					.memory()
					.expect("Memory must be set when setting up host data; qed")
					.data_and_store_mut(&mut __caller__);
				#body
			} }
		} else {
			quote! { || -> #wasm_output {
				// This is part of the implementation for `Environment<()>` which is not
				// meant to be actually executed. It is only for validation which will
				// never call host functions.
				::core::unreachable!()
			} }
		};
		let map_err = if expand_blocks {
			quote! {
				|reason| {
					::wasmi::core::Trap::host(reason)
				}
			}
		} else {
			quote! {
				|reason| { reason }
			}
		};
		let allow_unused =  if expand_blocks {
			quote! { }
		} else {
			quote! { #[allow(unused_variables)] }
		};

		quote! {
			// We need to allow unstable functions when runtime benchmarks are performed because
			// we generate the weights even when those interfaces are not enabled.
			if ::core::cfg!(feature = "runtime-benchmarks") || #is_stable || allow_unstable {
				#allow_unused
				linker.define(#module, #name, ::wasmi::Func::wrap(&mut*store, |mut __caller__: ::wasmi::Caller<#host_state>, #( #params, )*| -> #wasm_output {
					let mut func = #inner;
					func()
						.map_err(#map_err)
						.map(::core::convert::Into::into)
				}))?;
			}
		}
	});
	quote! {
		#( #impls )*
	}
}

/// Defines a host functions set that can be imported by contract wasm code.
///
/// **NB**: Be advised that all functions defined by this macro
/// will panic if called with unexpected arguments.
///
/// It's up to you as the user of this macro to check signatures of wasm code to be executed
/// and reject the code if any imported function has a mismatched signature.
///
/// ## Example
///
/// ```nocompile
/// #[define_env]
/// pub mod some_env {
/// 	fn foo(ctx: _, memory: _, key_ptr: u32, value_ptr: u32, value_len: u32) -> Result<(), TrapReason> {
/// 		ctx.some_host_fn(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
/// 	}
/// }
/// ```
/// This example will expand to the `foo()` defined in the wasm module named `seal0`. This is
/// because the module `seal0` is the default when no module is specified.
///
/// To define a host function in `seal2` and `seal3` modules, it should be annotated with the
/// appropriate attribute as follows:
///
/// ## Example
///
/// ```nocompile
/// #[define_env]
/// pub mod some_env {
/// 	#[version(2)]
/// 	fn foo(ctx: _, memory: _, key_ptr: u32, value_ptr: u32, value_len: u32) -> Result<ReturnCode, TrapReason> {
/// 		ctx.some_host_fn(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
/// 	}
///
/// 	#[version(3)]
/// 	#[unstable]
/// 	fn bar(ctx: _, memory: _, key_ptr: u32, value_ptr: u32, value_len: u32) -> Result<u32, TrapReason> {
/// 		ctx.some_host_fn(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
/// 	}
/// }
/// ```
/// The function `bar` is additionally annotated with `unstable` which removes it from the stable
/// interface. Check out the README to learn about unstable functions.
///
/// In legacy versions of pallet_contracts, it was a naming convention that all host functions had
/// to be named with the `seal_` prefix. For the sake of backwards compatibility, each host function
/// now can get a such prefix-named alias function generated by marking it by the
/// `#[prefixed_alias]` attribute:
///
/// ## Example
///
/// ```nocompile
/// #[define_env]
/// pub mod some_env {
/// 	#[version(1)]
/// 	#[prefixed_alias]
/// 	fn foo(ctx: _, memory: _, key_ptr: u32, value_ptr: u32, value_len: u32) -> Result<ReturnCode, TrapReason> {
/// 		ctx.some_host_fn(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
/// 	}
///
/// 	#[version(42)]
/// 	fn bar(ctx: _, memory: _, key_ptr: u32, value_ptr: u32, value_len: u32) -> Result<u32, TrapReason> {
/// 		ctx.some_host_fn(KeyType::Fix, key_ptr, value_ptr, value_len).map(|_| ())
/// 	}
/// }
/// ```
///
/// In this example, the following host functions will be generated by the macro:
/// - `foo()` in module `seal1`,
/// - `seal_foo()` in module `seal1`,
/// - `bar()` in module `seal42`.
///
/// Only following return types are allowed for the host functions defined with the macro:
/// - `Result<(), TrapReason>`,
/// - `Result<ReturnCode, TrapReason>`,
/// - `Result<u32, TrapReason>`.
///
/// The macro expands to `pub struct Env` declaration, with the following traits implementations:
/// - `pallet_contracts::wasm::Environment<Runtime<E>> where E: Ext`
/// - `pallet_contracts::wasm::Environment<()>`
///
/// The implementation on `()` can be used in places where no `Ext` exists, yet. This is useful
/// when only checking whether a code can be instantiated without actually executing any code.
#[proc_macro_attribute]
pub fn define_env(attr: TokenStream, item: TokenStream) -> TokenStream {
	if !attr.is_empty() {
		let msg = "Invalid `define_env` attribute macro: expected no attributes: `#[define_env]`.";
		let span = TokenStream2::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into()
	}

	let item = syn::parse_macro_input!(item as syn::ItemMod);

	match EnvDef::try_from(item) {
		Ok(mut def) => expand_env(&mut def).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
