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
	interface,
	interface::parse::{definition::selector, helper},
};
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use std::collections::HashMap;
use syn::spanned::Spanned;

pub struct CallDef {
	calls: Vec<SingleCallDef>,
}

impl CallDef {
	pub fn try_from(
		calls: Option<Self>,
		global_selector: bool,
		attr_span: proc_macro2::Span,
		_index: usize,
		item: &mut syn::TraitItem,
	) -> syn::Result<Self> {
		let method = if let syn::TraitItem::Method(method) = item {
			method
		} else {
			return Err(syn::Error::new(
				attr_span,
				"Invalid interface::call, expected item trait method",
			))
		};

		let mut calls = calls.unwrap_or(CallDef { calls: vec![] });
		let mut indices = HashMap::new();
		calls.calls.iter().for_each(|call| {
			// Below logic ensures assert won't fail
			assert!(indices.insert(call.call_index, call.name.clone()).is_none());
		});

		match method.sig.inputs.first() {
			None => {
				let msg = "Invalid interface::call, must have at least origin arg";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Receiver(_)) => {
				let msg = "Invalid interface::call, first argument must be a typed argument, \
							e.g. `origin: Self::RuntimeOrigin`";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Typed(arg)) => {
				check_call_first_arg_type(&arg.ty)?;
			},
		}

		if let syn::ReturnType::Type(_, ty) = &method.sig.output {
			check_call_return_type(ty)?;
		} else {
			let msg = "Invalid Interface::call, require return type \
						InterfaceResult";
			return Err(syn::Error::new(method.sig.span(), msg))
		}

		let (mut weight_attrs, mut call_idx_attrs, selector_attrs): (
			Vec<CallAttr>,
			Vec<CallAttr>,
			Vec<CallAttr>,
		) = helper::take_item_interface_attrs(&mut method.attrs)?.into_iter().try_fold(
			(Vec::new(), Vec::new(), Vec::new()),
			|(mut weight_attrs, mut call_idx_attrs, mut selector_attrs), attr| {
				match attr {
					CallAttr::Index(_) => call_idx_attrs.push(attr),
					CallAttr::Weight(_) => weight_attrs.push(attr),
					CallAttr::NoSelector | CallAttr::UseSelector(_) => {
						if !global_selector {
							let msg = "Invalid interface::view, selector attributes given \
								but top level mod misses `#[interface::with_selector] attribute.`";
							return Err(syn::Error::new(method.sig.span(), msg))
						}
						selector_attrs.push(attr)
					},
				}

				Ok((weight_attrs, call_idx_attrs, selector_attrs))
			},
		)?;

		if weight_attrs.len() != 1 {
			let msg = if weight_attrs.is_empty() {
				"Invalid interface::call, requires weight attribute i.e. `#[interface::weight($expr)]`"
			} else {
				"Invalid interface::call, too many weight attributes given"
			};
			return Err(syn::Error::new(method.sig.span(), msg))
		}
		let weight = match weight_attrs.pop().unwrap() {
			CallAttr::Weight(w) => w,
			_ => unreachable!("checked during creation of the let binding"),
		};

		if call_idx_attrs.len() != 1 {
			let msg = if call_idx_attrs.is_empty() {
				"Invalid interface::call, requires call_index attribute i.e. `#[interface::call_index(u8)]`"
			} else {
				"Invalid interface::call, too many call_index attributes given"
			};
			return Err(syn::Error::new(method.sig.span(), msg))
		}
		let call_index = match call_idx_attrs.pop().unwrap() {
			CallAttr::Index(idx) => idx,
			_ => unreachable!("checked during creation of the let binding"),
		};
		if let Some(used_fn) = indices.insert(call_index, method.sig.ident.clone()) {
			let msg = format!(
				"Call indices are conflicting: Both functions {} and {} are at index {}",
				used_fn, method.sig.ident, call_index,
			);
			let mut err = syn::Error::new(used_fn.span(), &msg);
			err.combine(syn::Error::new(method.sig.ident.span(), msg));
			return Err(err)
		}

		if selector_attrs.len() != 1 {
			let msg = "Invalid interface::call, too many selector attributes given.\
				Only use either `#[interface::no_selector]` `#[interface::use_selector($ident)]`";
			return Err(syn::Error::new(method.sig.span(), msg))
		};
		let with_selector = match selector_attrs.first() {
			Some(attr) => match attr {
				CallAttr::UseSelector(_) => true,
				CallAttr::NoSelector => false,
				_ => unreachable!("checked during creation of the let binding"),
			},
			None => global_selector,
		};

		let (skip, selector) = if with_selector {
			let first_arg_ty = match method.sig.inputs.first() {
				None => {
					let msg =
						"Invalid interface::view, must have `Select<$ty>` as first argument if \
						used with a selector and not annotated with #[interface::no_selector].";
					return Err(syn::Error::new(method.sig.span(), msg))
				},
				Some(syn::FnArg::Receiver(_)) => {
					let msg = "Invalid interface::view, second argument must be a typed argument, \
							e.g. `select: Select<$ty>`";
					return Err(syn::Error::new(method.sig.span(), msg))
				},
				Some(syn::FnArg::Typed(arg)) => check_call_second_arg_type(&arg.ty)?,
			};

			let selector_ty = match selector_attrs.first() {
				Some(attr) => match attr {
					CallAttr::UseSelector(name) => interface::SelectorType::Named {
						name: name.clone(),
						return_ty: first_arg_ty,
					},
					CallAttr::NoSelector =>
						unreachable!("checked during creation of the let binding"),
					_ => unreachable!("checked during creation of the let binding"),
				},
				None => interface::SelectorType::Default { return_ty: first_arg_ty },
			};

			(2, Some(selector_ty))
		} else {
			(1, None)
		};

		// Skip first
		// Skip second if with_selector
		let mut args = vec![];
		for arg in method.sig.inputs.iter_mut().skip(skip) {
			let arg = if let syn::FnArg::Typed(arg) = arg {
				arg
			} else {
				unreachable!("Only first argument can be receiver");
			};

			let arg_attrs: Vec<ArgAttrIsCompact> =
				helper::take_item_interface_attrs(&mut arg.attrs)?;

			if arg_attrs.len() > 1 {
				let msg = "Invalid interface::call, argument has too many attributes";
				return Err(syn::Error::new(arg.span(), msg))
			}

			let arg_ident = if let syn::Pat::Ident(pat) = &*arg.pat {
				pat.ident.clone()
			} else {
				let msg = "Invalid interface::call, argument must be ident";
				return Err(syn::Error::new(arg.pat.span(), msg))
			};

			args.push((!arg_attrs.is_empty(), arg_ident, arg.ty.clone()));
		}

		let docs = get_doc_literals(&method.attrs);

		calls.calls.push(SingleCallDef {
			selector,
			name: method.sig.ident.clone(),
			weight,
			call_index,
			args,
			docs,
			attrs: method.attrs.clone(),
			attr_span,
		});

		Ok(calls)
	}
}

pub struct SingleCallDef {
	/// Signal whether second argument must
	/// be a selector
	selector: Option<interface::SelectorType>,
	/// Function name.
	name: syn::Ident,
	/// Information on args: `(is_compact, name, type)`
	args: Vec<(bool, syn::Ident, Box<syn::Type>)>,
	/// Weight formula.
	weight: syn::Expr,
	/// Call index of the interface.
	call_index: u8,
	/// Docs, used for metadata.
	docs: Vec<syn::Lit>,
	/// Attributes annotated at the top of the dispatchable function.
	attrs: Vec<syn::Attribute>,
	/// The span of the call definition
	attr_span: proc_macro2::Span,
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(no_selector);
	syn::custom_keyword!(use_selector);
	syn::custom_keyword!(call_index);
	syn::custom_keyword!(weight);
	syn::custom_keyword!(RuntimeOrigin);
	syn::custom_keyword!(InterfaceResult);
	syn::custom_keyword!(compact);
	syn::custom_keyword!(Select);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::call]`)
enum CallAttr {
	Index(u8),
	Weight(syn::Expr),
	UseSelector(syn::Ident),
	NoSelector,
}

impl syn::parse::Parse for CallAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::call_index) {
			content.parse::<keyword::call_index>()?;
			let call_index_content;
			syn::parenthesized!(call_index_content in content);
			let index = call_index_content.parse::<syn::LitInt>()?;
			if !index.suffix().is_empty() {
				let msg = "Number literal must not have a suffix";
				return Err(syn::Error::new(index.span(), msg))
			}
			Ok(CallAttr::Index(index.base10_parse()?))
		} else if lookahead.peek(keyword::use_selector) {
			content.parse::<keyword::use_selector>()?;
			let use_selector_content;
			syn::parenthesized!(use_selector_content in content);
			Ok(CallAttr::UseSelector(use_selector_content.parse::<syn::Ident>()?))
		} else if lookahead.peek(keyword::no_selector) {
			content.parse::<keyword::no_selector>()?;
			Ok(CallAttr::NoSelector)
		} else if lookahead.peek(keyword::weight) {
			content.parse::<keyword::weight>()?;
			let weight_content;
			syn::parenthesized!(weight_content in content);
			Ok(CallAttr::Weight(weight_content.parse::<syn::Expr>()?))
		} else {
			Err(lookahead.error())
		}
	}
}

/// Check the syntax is `Self::RuntimeOrigin`
pub fn check_call_first_arg_type(ty: &syn::Type) -> syn::Result<()> {
	pub struct CheckCallFirstArg;
	impl syn::parse::Parse for CheckCallFirstArg {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<syn::token::SelfType>()?;
			input.parse::<syn::Token![::]>()?;
			input.parse::<keyword::RuntimeOrigin>()?;

			Ok(Self)
		}
	}

	syn::parse2::<CheckCallFirstArg>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `Self::RuntimeOrigin`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(())
}

/// Check the syntax is `Select<$ident>`
pub fn check_call_second_arg_type(ty: &syn::Type) -> syn::Result<Box<syn::Type>> {
	pub struct CheckCallSecondArg(Box<syn::Type>);
	impl syn::parse::Parse for CheckCallSecondArg {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<keyword::Select>()?;
			input.parse::<syn::Token![<]>()?;
			let ty = input.parse::<syn::Type>()?;
			input.parse::<syn::Token![>]>()?;
			Ok(Self(Box::new(ty)))
		}
	}

	let check = syn::parse2::<CheckCallSecondArg>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `Select<$ident>`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(check.0)
}

/// Check the keyword `InterfaceResult`.
pub fn check_call_return_type(type_: &syn::Type) -> syn::Result<()> {
	pub struct Checker;
	impl syn::parse::Parse for Checker {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			let lookahead = input.lookahead1();
			if lookahead.peek(keyword::InterfaceResult) {
				input.parse::<keyword::InterfaceResult>()?;
				Ok(Self)
			} else {
				Err(lookahead.error())
			}
		}
	}

	syn::parse2::<Checker>(type_.to_token_stream()).map(|_| ())
}

/// Attribute for arguments in function in call impl block.
/// Parse for `#[interface::compact]|
pub struct ArgAttrIsCompact;

impl syn::parse::Parse for ArgAttrIsCompact {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;
		content.parse::<keyword::compact>()?;
		Ok(ArgAttrIsCompact)
	}
}
