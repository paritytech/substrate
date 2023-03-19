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

use crate::interface::parse::helper;
use quote::ToTokens;
use syn::spanned::Spanned;

pub struct SelectorDef {
	selectors: Vec<SingleSelectorDef>,
}

impl SelectorDef {
	pub fn try_from(
		selectors: Option<SelectorDef>,
		name: syn::Ident,
		attr_span: proc_macro2::Span,
		_index: usize,
		item: &mut syn::TraitItem,
	) -> syn::Result<Self> {
		let method = if let syn::TraitItem::Method(method) = item {
			method
		} else {
			return Err(syn::Error::new(
				attr_span,
				"Invalid interface::selector($ident), expected item trait method",
			))
		};

		let mut selectors = selectors.unwrap_or(SelectorDef { selectors: Vec::new() });

		match method.sig.inputs.first() {
			None => {
				let msg = "Invalid interface::selector, must exactly one arg Self::Selectable";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Receiver(_)) => {
				let msg = "Invalid interface::selector, first argument must be a typed argument, \
							e.g. `selectable: Self::Selectable`";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Typed(arg)) => {
				check_selector_first_arg_type(&arg.ty)?;
			},
		}

		let default_attr: Option<SelectorAttr> = helper::take_item_interface_attrs(
			&mut method.attrs,
		)?
		.into_iter()
		.try_fold(None, |mut default_attr, attr| {
			match attr {
				SelectorAttr::DefaultSelector(_) if default_attr.is_none() => {
					default_attr = Some(attr);
				},
				_ => {
					let msg = "Invalid duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg))
				},
			}

			Ok(default_attr)
		})?;

		match method.sig.inputs.first() {
			None => {
				let msg = "Invalid interface::selector, must have only selectable arg.";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Receiver(_)) => {
				let msg = "Invalid interface::selector, first argument must be a typed argument, \
							e.g. `selectable: Self::Selectable`";
				return Err(syn::Error::new(method.sig.span(), msg))
			},
			Some(syn::FnArg::Typed(arg)) => {
				check_selector_first_arg_type(&arg.ty)?;
			},
		}

		let output = if let syn::ReturnType::Type(_, ty) = &method.sig.output {
			check_selector_return_type(ty)?
		} else {
			let msg = "Invalid Interface::selector, require return type \
						Result<$ty, InterfaceError>";
			return Err(syn::Error::new(method.sig.span(), msg))
		};

		selectors.push_and_check_default(SingleSelectorDef {
			name,
			output,
			attr_span,
			default: default_attr.is_some(),
		})?;

		Ok(selectors)
	}

	fn push_and_check_default(&mut self, selector: SingleSelectorDef) -> syn::Result<()> {
		if selector.default {
			if self.selectors.iter().any(|given_s| given_s.default) {
				let msg = "Invalid Interface::selector, duplicate \
						default selector attribute";
				return Err(syn::Error::new(selector.attr_span, msg))
			}
		}

		Ok(self.selectors.push(selector))
	}
}

pub struct SingleSelectorDef {
	/// Function name.
	name: syn::Ident,
	/// The return type of the selector.
	output: Box<syn::Type>,
	/// The span of the selector definition
	attr_span: proc_macro2::Span,
	/// Signal if default selector
	default: bool,
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(selector);
	syn::custom_keyword!(default_selector);
	syn::custom_keyword!(InterfaceError);
	syn::custom_keyword!(Result);
	syn::custom_keyword!(Selectable);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::selector]`)
enum SelectorAttr {
	DefaultSelector(proc_macro2::Span),
}

impl SelectorAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::DefaultSelector(span) => span.clone(),
		}
	}
}

impl syn::parse::Parse for SelectorAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::default_selector) {
			Ok(SelectorAttr::DefaultSelector(content.parse::<keyword::default_selector>()?.span()))
		} else {
			Err(lookahead.error())
		}
	}
}

/// Check the syntax is `Self::Selectable`
pub fn check_selector_first_arg_type(ty: &syn::Type) -> syn::Result<()> {
	pub struct CheckSelectorFirstArg;
	impl syn::parse::Parse for CheckSelectorFirstArg {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<syn::token::SelfType>()?;
			input.parse::<syn::Token![::]>()?;
			input.parse::<keyword::Selectable>()?;

			Ok(Self)
		}
	}

	syn::parse2::<CheckSelectorFirstArg>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `Self::Selectable`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(())
}

/// Check the return type is `Result<$type, InterfaceError>`
pub fn check_selector_return_type(ty: &syn::Type) -> syn::Result<Box<syn::Type>> {
	pub struct CheckSelectorReturnType(Box<syn::Type>);
	impl syn::parse::Parse for CheckSelectorReturnType {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<keyword::Result>()?;
			input.parse::<syn::Token![<]>()?;
			let ty = input.parse::<syn::Type>()?;
			input.parse::<syn::Token![,]>()?;
			input.parse::<keyword::InterfaceError>()?;
			input.parse::<syn::Token![>]>()?;
			Ok(Self(Box::new(ty)))
		}
	}

	let check = syn::parse2::<CheckSelectorReturnType>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `Result<$ident, InterfaceError>`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(check.0)
}
