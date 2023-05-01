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

//! Procedural macros used in the contracts module.
//!
//! Most likely you should use the [`#[define_env]`][`macro@define_env`] attribute macro which hides
//! boilerplate of defining external environment for a wasm module.

#![no_std]

extern crate alloc;

use alloc::{
	collections::BTreeMap,
	format,
	string::{String, ToString},
	vec::Vec,
};
use core::cmp::Reverse;
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
	parse_macro_input, punctuated::Punctuated, spanned::Spanned, token::Comma, Data, DeriveInput,
	FnArg, Ident,
};

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
		&if self.#field.ref_time() > 1_000_000_000 {
			format!(
				"{:.1?} ms, {} bytes",
				Fixed::saturating_from_rational(self.#field.ref_time(), 1_000_000_000).to_float(),
				self.#field.proof_size()
			)
		} else if self.#field.ref_time() > 1_000_000 {
			format!(
				"{:.1?} µs, {} bytes",
				Fixed::saturating_from_rational(self.#field.ref_time(), 1_000_000).to_float(),
				self.#field.proof_size()
			)
		} else if self.#field.ref_time() > 1_000 {
			format!(
				"{:.1?} ns, {} bytes",
				Fixed::saturating_from_rational(self.#field.ref_time(), 1_000).to_float(),
				self.#field.proof_size()
			)
		} else {
			format!("{} ps, {} bytes", self.#field.ref_time(), self.#field.proof_size())
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
	version: u8,
	name: String,
	returns: HostFnReturn,
	is_stable: bool,
	alias_to: Option<String>,
	/// Formulating the predicate inverted makes the expression using it simpler.
	not_deprecated: bool,
}

enum HostFnReturn {
	Unit,
	U32,
	U64,
	ReturnCode,
}

impl HostFnReturn {
	fn to_wasm_sig(&self) -> TokenStream2 {
		let ok = match self {
			Self::Unit => quote! { () },
			Self::U32 | Self::ReturnCode => quote! { ::core::primitive::u32 },
			Self::U64 => quote! { ::core::primitive::u64 },
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
	pub fn try_from(mut item: syn::ItemFn) -> syn::Result<Self> {
		let err = |span, msg| {
			let msg = format!("Invalid host function definition. {}", msg);
			syn::Error::new(span, msg)
		};

		// process attributes
		let msg =
			"only #[version(<u8>)], #[unstable], #[prefixed_alias] and #[deprecated] attributes are allowed.";
		let span = item.span();
		let mut attrs = item.attrs.clone();
		attrs.retain(|a| !a.path().is_ident("doc"));
		let mut maybe_version = None;
		let mut is_stable = true;
		let mut alias_to = None;
		let mut not_deprecated = true;
		while let Some(attr) = attrs.pop() {
			let ident = attr.path().get_ident().ok_or(err(span, msg))?.to_string();
			match ident.as_str() {
				"version" => {
					if maybe_version.is_some() {
						return Err(err(span, "#[version] can only be specified once"))
					}
					maybe_version =
						Some(attr.parse_args::<syn::LitInt>().and_then(|lit| lit.base10_parse())?);
				},
				"unstable" => {
					if !is_stable {
						return Err(err(span, "#[unstable] can only be specified once"))
					}
					is_stable = false;
				},
				"prefixed_alias" => {
					alias_to = Some(item.sig.ident.to_string());
					item.sig.ident = syn::Ident::new(
						&format!("seal_{}", &item.sig.ident.to_string()),
						item.sig.ident.span(),
					);
				},
				"deprecated" => {
					if !not_deprecated {
						return Err(err(span, "#[deprecated] can only be specified once"))
					}
					not_deprecated = false;
				},
				_ => return Err(err(span, msg)),
			}
		}
		let name = item.sig.ident.to_string();

		if !(is_stable || not_deprecated) {
			return Err(err(span, "#[deprecated] is mutually exclusive with #[unstable]"))
		}

		// process arguments: The first and second args are treated differently (ctx, memory)
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
				- Result<u64, TrapReason>,
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
							"u64" => Ok(HostFnReturn::U64),
							"ReturnCode" => Ok(HostFnReturn::ReturnCode),
							_ => Err(err(arg1.span(), &msg)),
						}?;

						Ok(Self {
							item,
							version: maybe_version.unwrap_or_default(),
							name,
							returns,
							is_stable,
							alias_to,
							not_deprecated,
						})
					},
					_ => Err(err(span, &msg)),
				}
			},
			_ => Err(err(span, &msg)),
		}
	}

	fn module(&self) -> String {
		format!("seal{}", self.version)
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

		let selector = |a: &syn::Attribute| a.path().is_ident("prefixed_alias");

		let aliases = items
			.iter()
			.filter_map(extract_fn)
			.filter(|i| i.attrs.iter().any(selector))
			.map(|i| HostFn::try_from(i));

		let host_funcs = items
			.iter()
			.filter_map(extract_fn)
			.map(|mut i| {
				i.attrs.retain(|i| !selector(i));
				i
			})
			.map(|i| HostFn::try_from(i))
			.chain(aliases)
			.collect::<Result<Vec<_>, _>>()?;

		Ok(Self { host_funcs })
	}
}

fn is_valid_special_arg(idx: usize, arg: &FnArg) -> bool {
	let FnArg::Typed(pat) = arg else { return false };
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

fn expand_func_doc(func: &HostFn) -> TokenStream2 {
	// Remove auxiliary args: `ctx: _` and `memory: _`
	let func_decl = {
		let mut sig = func.item.sig.clone();
		sig.inputs = sig
			.inputs
			.iter()
			.skip(2)
			.map(|p| p.clone())
			.collect::<Punctuated<FnArg, Comma>>();
		sig.to_token_stream()
	};
	let func_doc = {
		let func_docs = if let Some(origin_fn) = &func.alias_to {
			let alias_doc = format!(
				"This is just an alias function to [`{0}()`][`Self::{0}`] with backwards-compatible prefixed identifier.",
				origin_fn,
			);
			quote! { #[doc = #alias_doc] }
		} else {
			let docs = func.item.attrs.iter().filter(|a| a.path().is_ident("doc")).map(|d| {
				let docs = d.to_token_stream();
				quote! { #docs }
			});
			quote! { #( #docs )* }
		};
		let deprecation_notice = if !func.not_deprecated {
			let warning = "\n # Deprecated\n\n \
								This function is deprecated and will be removed in future versions.\n \
								No new code or contracts with this API can be deployed.";
			quote! { #[doc = #warning] }
		} else {
			quote! {}
		};
		let import_notice = {
			let info = format!(
				"\n# Wasm Import Statement\n```wat\n(import \"seal{}\" \"{}\" (func ...))\n```",
				func.version, func.name,
			);
			quote! { #[doc = #info] }
		};
		let unstable_notice = if !func.is_stable {
			let warning = "\n # Unstable\n\n \
								This function is unstable and it is a subject to change (or removal) in the future.\n \
								Do not deploy a contract using it to a production chain.";
			quote! { #[doc = #warning] }
		} else {
			quote! {}
		};
		quote! {
			#deprecation_notice
			#func_docs
			#import_notice
			#unstable_notice
		}
	};
	quote! {
		#func_doc
		#func_decl;
	}
}

/// Expands documentation for host functions.
fn expand_docs(def: &EnvDef) -> TokenStream2 {
	// Create the `Current` trait with only the newest versions
	// we sort so that only the newest versions make it into `docs`
	let mut current_docs = BTreeMap::new();
	let mut funcs: Vec<_> = def.host_funcs.iter().filter(|f| f.alias_to.is_none()).collect();
	funcs.sort_unstable_by_key(|func| Reverse(func.version));
	for func in funcs {
		if current_docs.contains_key(&func.name) {
			continue
		}
		current_docs.insert(func.name.clone(), expand_func_doc(&func));
	}
	let current_docs = current_docs.values();

	// Create the `legacy` module with all functions
	// Maps from version to list of functions that have this version
	let mut legacy_doc = BTreeMap::<u8, Vec<TokenStream2>>::new();
	for func in def.host_funcs.iter() {
		legacy_doc.entry(func.version).or_default().push(expand_func_doc(&func));
	}
	let legacy_doc = legacy_doc.into_iter().map(|(version, funcs)| {
		let doc = format!("All functions available in the **seal{}** module", version);
		let version = Ident::new(&format!("Version{version}"), Span::call_site());
		quote! {
			#[doc = #doc]
			pub trait #version {
				#( #funcs )*
			}
		}
	});

	quote! {
		/// Contains only the latest version of each function.
		///
		/// In reality there are more functions available but they are all obsolete: When a function
		/// is updated a new **version** is added and the old versions stays available as-is.
		/// We only list the newest version here. Some functions are available under additional
		/// names (aliases) for historic reasons which are omitted here.
		///
		/// If you want an overview of all the functions available to a contact all you need
		/// to look at is this trait. It contains only the latest version of each
		/// function and no aliases. If you are writing a contract(language) from scratch
		/// this is where you should look at.
		pub trait Current {
			#( #current_docs )*
		}
		#( #legacy_doc )*
	}
}

/// Expands environment definition.
/// Should generate source code for:
///  - implementations of the host functions to be added to the wasm runtime environment (see
///    `expand_impls()`).
fn expand_env(def: &EnvDef, docs: bool) -> TokenStream2 {
	let impls = expand_impls(def);
	let docs = docs.then_some(expand_docs(def)).unwrap_or(TokenStream2::new());

	quote! {
		pub struct Env;
		#impls
		/// Documentation of the API (host functions) available to contracts.
		///
		/// The `Current` trait might be the most useful doc to look at. The versioned
		/// traits only exist for reference: If trying to find out if a specific version of
		/// `pallet-contracts` contains a certain function.
		///
		/// # Note
		///
		/// This module is not meant to be used by any code. Rather, it is meant to be
		/// consumed by humans through rustdoc.
		#[cfg(doc)]
		pub mod api_doc {
			use super::{TrapReason, ReturnCode};
			#docs
		}
	}
}

/// Generates for every host function:
///   - real implementation, to register it in the contract execution environment;
///   - dummy implementation, to be used as mocks for contract validation step.
fn expand_impls(def: &EnvDef) -> TokenStream2 {
	let impls = expand_functions(def, true, quote! { crate::wasm::Runtime<E> });
	let dummy_impls = expand_functions(def, false, quote! { () });

	quote! {
		impl<'a, E: Ext> crate::wasm::Environment<crate::wasm::runtime::Runtime<'a, E>> for Env
		{
			fn define(
				store: &mut ::wasmi::Store<crate::wasm::Runtime<E>>,
				linker: &mut ::wasmi::Linker<crate::wasm::Runtime<E>>,
				allow_unstable: AllowUnstableInterface,
				allow_deprecated: AllowDeprecatedInterface,
			) -> Result<(),::wasmi::errors::LinkerError> {
				#impls
				Ok(())
			}
		}

		impl crate::wasm::Environment<()> for Env
		{
			fn define(
				store: &mut ::wasmi::Store<()>,
				linker: &mut ::wasmi::Linker<()>,
				allow_unstable: AllowUnstableInterface,
				allow_deprecated: AllowDeprecatedInterface,
			) -> Result<(), ::wasmi::errors::LinkerError> {
				#dummy_impls
				Ok(())
			}
		}
	}
}

fn expand_functions(def: &EnvDef, expand_blocks: bool, host_state: TokenStream2) -> TokenStream2 {
	let impls = def.host_funcs.iter().map(|f| {
		// skip the context and memory argument
		let params = f.item.sig.inputs.iter().skip(2);

		let (module, name, body, wasm_output, output) = (
			f.module(),
			&f.name,
			&f.item.block,
			f.returns.to_wasm_sig(),
			&f.item.sig.output
		);
		let is_stable = f.is_stable;
		let not_deprecated = f.not_deprecated;

		// wrapped host function body call with host function traces
		// see https://github.com/paritytech/substrate/tree/master/frame/contracts#host-function-tracing
		let wrapped_body_with_trace = {
			let trace_fmt_args = params.clone().filter_map(|arg| match arg {
				syn::FnArg::Receiver(_) => None,
				syn::FnArg::Typed(p) => {
					match *p.pat.clone() {
						syn::Pat::Ident(ref pat_ident) => Some(pat_ident.ident.clone()),
						_ => None,
					}
				},
			});

			let params_fmt_str = trace_fmt_args.clone().map(|s| format!("{s}: {{:?}}")).collect::<Vec<_>>().join(", ");
			let trace_fmt_str = format!("{}::{}({}) = {{:?}}\n", module, name, params_fmt_str);

			quote! {
				if ::log::log_enabled!(target: "runtime::contracts::strace", ::log::Level::Trace) {
					let result = #body;
					{
						use sp_std::fmt::Write;
						let mut w = sp_std::Writer::default();
						let _ = core::write!(&mut w, #trace_fmt_str, #( #trace_fmt_args, )* result);
						let msg = core::str::from_utf8(&w.inner()).unwrap_or_default();
						ctx.ext().append_debug_buffer(msg);
					}
					result
				} else {
					#body
				}
			}
		};

		// If we don't expand blocks (implementing for `()`) we change a few things:
		// - We replace any code by unreachable!
		// - Allow unused variables as the code that uses is not expanded
		// - We don't need to map the error as we simply panic if they code would ever be executed
		let inner = if expand_blocks {
			quote! { || #output {
				let (memory, ctx) = __caller__
					.data()
					.memory()
					.expect("Memory must be set when setting up host data; qed")
					.data_and_store_mut(&mut __caller__);
				#wrapped_body_with_trace
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
					::wasmi::core::Trap::from(reason)
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
			// We need to allow all interfaces when runtime benchmarks are performed because
			// we generate the weights even when those interfaces are not enabled. This
			// is necessary as the decision whether we allow unstable or deprecated functions
			// is a decision made at runtime. Generation of the weights happens statically.
			if ::core::cfg!(feature = "runtime-benchmarks") ||
				((#is_stable || __allow_unstable__) && (#not_deprecated || __allow_deprecated__))
			{
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
		let __allow_unstable__ = matches!(allow_unstable, AllowUnstableInterface::Yes);
		let __allow_deprecated__ = matches!(allow_deprecated, AllowDeprecatedInterface::Yes);
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
///
/// # Generating Documentation
///
/// Passing `doc` attribute to the macro (like `#[define_env(doc)]`) will make it also expand
/// additional `pallet_contracts::api_doc::seal0`, `pallet_contracts::api_doc::seal1`,
/// `...` modules each having its `Api` trait containing functions holding documentation for every
/// host function defined by the macro.
///
/// # Deprecated Interfaces
///
/// An interface can be annotated with `#[deprecated]`. It is mutually exclusive with `#[unstable]`.
/// Deprecated interfaces have the following properties:
/// 	- New contract codes utilizing those interfaces cannot be uploaded.
/// 	- New contracts from existing codes utilizing those interfaces cannot be instantiated.
/// - Existing contracts containing those interfaces still work.
///
/// Those interfaces will eventually be removed.
///
/// To build up these docs, run:
///
/// ```nocompile
/// cargo doc
/// ```
#[proc_macro_attribute]
pub fn define_env(attr: TokenStream, item: TokenStream) -> TokenStream {
	if !attr.is_empty() && !(attr.to_string() == "doc".to_string()) {
		let msg = r#"Invalid `define_env` attribute macro: expected either no attributes or a single `doc` attribute:
					 - `#[define_env]`
					 - `#[define_env(doc)]`"#;
		let span = TokenStream2::from(attr).span();
		return syn::Error::new(span, msg).to_compile_error().into()
	}

	let item = syn::parse_macro_input!(item as syn::ItemMod);

	match EnvDef::try_from(item) {
		Ok(mut def) => expand_env(&mut def, !attr.is_empty()).into(),
		Err(e) => e.to_compile_error().into(),
	}
}
