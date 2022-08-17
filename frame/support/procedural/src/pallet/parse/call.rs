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

use super::helper;
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use std::collections::HashMap;
use syn::spanned::Spanned;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(Call);
	syn::custom_keyword!(OriginFor);
	syn::custom_keyword!(weight);
	syn::custom_keyword!(call_index);
	syn::custom_keyword!(compact);
	syn::custom_keyword!(T);
	syn::custom_keyword!(pallet);
}

/// Definition of dispatchables typically `impl<T: Config> Pallet<T> { ... }`
pub struct CallDef {
	/// The where_clause used.
	pub where_clause: Option<syn::WhereClause>,
	/// A set of usage of instance, must be check for consistency with trait.
	pub instances: Vec<helper::InstanceUsage>,
	/// The index of call item in pallet module.
	pub index: usize,
	/// Information on methods (used for expansion).
	pub methods: Vec<CallVariantDef>,
	/// The span of the pallet::call attribute.
	pub attr_span: proc_macro2::Span,
	/// Docs, specified on the impl Block.
	pub docs: Vec<syn::Lit>,
}

/// Definition of dispatchable typically: `#[weight...] fn foo(origin .., param1: ...) -> ..`
#[derive(Clone)]
pub struct CallVariantDef {
	/// Function name.
	pub name: syn::Ident,
	/// Information on args: `(is_compact, name, type)`
	pub args: Vec<(bool, syn::Ident, Box<syn::Type>)>,
	/// Weight formula.
	pub weight: syn::Expr,
	/// Call index of the dispatchable.
	pub call_index: u8,
	/// Docs, used for metadata.
	pub docs: Vec<syn::Lit>,
}

/// Attributes for functions in call impl block.
/// Parse for `#[pallet::weight(expr)]` or `#[pallet::call_index(expr)]
pub enum FunctionAttr {
	CallIndex(u8),
	Weight(syn::Expr),
}

impl syn::parse::Parse for FunctionAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::weight) {
			content.parse::<keyword::weight>()?;
			let weight_content;
			syn::parenthesized!(weight_content in content);
			Ok(FunctionAttr::Weight(weight_content.parse::<syn::Expr>()?))
		} else if lookahead.peek(keyword::call_index) {
			content.parse::<keyword::call_index>()?;
			let call_index_content;
			syn::parenthesized!(call_index_content in content);
			let index = call_index_content.parse::<syn::LitInt>()?;
			Ok(FunctionAttr::CallIndex(index.base10_parse()?))
		} else {
			Err(lookahead.error())
		}
	}
}

/// Attribute for arguments in function in call impl block.
/// Parse for `#[pallet::compact]|
pub struct ArgAttrIsCompact;

impl syn::parse::Parse for ArgAttrIsCompact {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;

		content.parse::<keyword::compact>()?;
		Ok(ArgAttrIsCompact)
	}
}

/// Check the syntax is `OriginFor<T>`
pub fn check_dispatchable_first_arg_type(ty: &syn::Type) -> syn::Result<()> {
	pub struct CheckDispatchableFirstArg;
	impl syn::parse::Parse for CheckDispatchableFirstArg {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<keyword::OriginFor>()?;
			input.parse::<syn::Token![<]>()?;
			input.parse::<keyword::T>()?;
			input.parse::<syn::Token![>]>()?;

			Ok(Self)
		}
	}

	syn::parse2::<CheckDispatchableFirstArg>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `OriginFor<T>`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(())
}

impl CallDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item_impl = if let syn::Item::Impl(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::call, expected item impl"))
		};

		let instances = vec![
			helper::check_impl_gen(&item_impl.generics, item_impl.impl_token.span())?,
			helper::check_pallet_struct_usage(&item_impl.self_ty)?,
		];

		if let Some((_, _, for_)) = item_impl.trait_ {
			let msg = "Invalid pallet::call, expected no trait ident as in \
				`impl<..> Pallet<..> { .. }`";
			return Err(syn::Error::new(for_.span(), msg))
		}

		let mut methods = vec![];
		let mut indices = HashMap::new();
		let mut last_index: Option<u8> = None;
		for item in &mut item_impl.items {
			if let syn::ImplItem::Method(method) = item {
				if !matches!(method.vis, syn::Visibility::Public(_)) {
					let msg = "Invalid pallet::call, dispatchable function must be public: \
						`pub fn`";

					let span = match method.vis {
						syn::Visibility::Inherited => method.sig.span(),
						_ => method.vis.span(),
					};

					return Err(syn::Error::new(span, msg))
				}

				match method.sig.inputs.first() {
					None => {
						let msg = "Invalid pallet::call, must have at least origin arg";
						return Err(syn::Error::new(method.sig.span(), msg))
					},
					Some(syn::FnArg::Receiver(_)) => {
						let msg = "Invalid pallet::call, first argument must be a typed argument, \
							e.g. `origin: OriginFor<T>`";
						return Err(syn::Error::new(method.sig.span(), msg))
					},
					Some(syn::FnArg::Typed(arg)) => {
						check_dispatchable_first_arg_type(&arg.ty)?;
					},
				}

				if let syn::ReturnType::Type(_, type_) = &method.sig.output {
					helper::check_pallet_call_return_type(type_)?;
				} else {
					let msg = "Invalid pallet::call, require return type \
						DispatchResultWithPostInfo";
					return Err(syn::Error::new(method.sig.span(), msg))
				}

				let (mut weight_attrs, mut call_idx_attrs): (Vec<FunctionAttr>, Vec<FunctionAttr>) =
					helper::take_item_pallet_attrs(&mut method.attrs)?.into_iter().partition(
						|attr| {
							if let FunctionAttr::Weight(_) = attr {
								true
							} else {
								false
							}
						},
					);

				if weight_attrs.len() != 1 {
					let msg = if weight_attrs.is_empty() {
						"Invalid pallet::call, requires weight attribute i.e. `#[pallet::weight($expr)]`"
					} else {
						"Invalid pallet::call, too many weight attributes given"
					};
					return Err(syn::Error::new(method.sig.span(), msg))
				}
				let weight = match weight_attrs.pop().unwrap() {
					FunctionAttr::Weight(w) => w,
					_ => unreachable!("checked during creation of the let binding"),
				};

				if call_idx_attrs.len() > 1 {
					let msg = "Invalid pallet::call, too many call_index attributes given";
					return Err(syn::Error::new(method.sig.span(), msg))
				}
				let call_index = call_idx_attrs.pop().map(|attr| match attr {
					FunctionAttr::CallIndex(idx) => idx,
					_ => unreachable!("checked during creation of the let binding"),
				});

				let final_index = match call_index {
					Some(i) => i,
					None =>
						last_index.map_or(Some(0), |idx| idx.checked_add(1)).ok_or_else(|| {
							let msg = "Call index doesn't fit into u8, index is 256";
							syn::Error::new(method.sig.span(), msg)
						})?,
				};
				last_index = Some(final_index);

				if let Some(used_fn) = indices.insert(final_index, method.sig.ident.clone()) {
					let msg = format!(
						"Call indices are conflicting: Both functions {} and {} are at index {}",
						used_fn, method.sig.ident, final_index,
					);
					let mut err = syn::Error::new(used_fn.span(), &msg);
					err.combine(syn::Error::new(method.sig.ident.span(), msg));
					return Err(err)
				}

				let mut args = vec![];
				for arg in method.sig.inputs.iter_mut().skip(1) {
					let arg = if let syn::FnArg::Typed(arg) = arg {
						arg
					} else {
						unreachable!("Only first argument can be receiver");
					};

					let arg_attrs: Vec<ArgAttrIsCompact> =
						helper::take_item_pallet_attrs(&mut arg.attrs)?;

					if arg_attrs.len() > 1 {
						let msg = "Invalid pallet::call, argument has too many attributes";
						return Err(syn::Error::new(arg.span(), msg))
					}

					let arg_ident = if let syn::Pat::Ident(pat) = &*arg.pat {
						pat.ident.clone()
					} else {
						let msg = "Invalid pallet::call, argument must be ident";
						return Err(syn::Error::new(arg.pat.span(), msg))
					};

					args.push((!arg_attrs.is_empty(), arg_ident, arg.ty.clone()));
				}

				let docs = get_doc_literals(&method.attrs);

				methods.push(CallVariantDef {
					name: method.sig.ident.clone(),
					weight,
					call_index: final_index,
					args,
					docs,
				});
			} else {
				let msg = "Invalid pallet::call, only method accepted";
				return Err(syn::Error::new(item.span(), msg))
			}
		}

		Ok(Self {
			index,
			attr_span,
			instances,
			methods,
			where_clause: item_impl.generics.where_clause.clone(),
			docs: get_doc_literals(&item_impl.attrs),
		})
	}
}
