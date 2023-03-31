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

use crate::interface::{
	definition,
	definition::parse::{definition::selector::SelectorDef, helper},
};
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use std::collections::HashMap;
use syn::spanned::Spanned;

pub struct ViewDef {
	pub interface_span: proc_macro2::Span,
	pub views: Vec<SingleViewDef>,
}

impl ViewDef {
	pub fn try_from(
		interface_span: proc_macro2::Span,
		views: Option<Self>,
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
				"Invalid interface::view, expected item trait method",
			))
		};

		let mut views = views.unwrap_or(ViewDef { interface_span, views: vec![] });
		let mut indices = HashMap::new();
		views.views.iter().for_each(|view| {
			// Below logic ensures assert won't fail
			assert!(indices.insert(view.view_index, view.name.clone()).is_none());
		});

		let (mut view_idx_attrs, selector_attr): (Vec<ViewAttr>, Option<ViewAttr>) =
			helper::take_item_interface_attrs(&mut method.attrs)?.into_iter().try_fold(
				(Vec::new(), None),
				|(mut view_idx_attrs, mut selector_attr), attr| {
					match attr {
						ViewAttr::Index(_) => view_idx_attrs.push(attr),
						ViewAttr::NoSelector => {
							if !global_selector {
								let msg = "Invalid interface::view, selector attributes given \
								but top level mod misses `#[interface::with_selector] attribute.`";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							if let Some(ViewAttr::UseSelector(_)) = selector_attr {
								let msg =
									"Invalid interface::view, both `#[interface::no_selector]` and \
								`#[interface::use_selector($ident)]` used on the same method. Use either one or the other";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							if selector_attr.is_some() {
								let msg =
									"Invalid interface::view, multiple `#[interface::no_selector]` \
								attributes used on the same method. Only one is allowed.";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							selector_attr = Some(attr);
						},
						ViewAttr::UseSelector(_) => {
							if !global_selector {
								let msg = "Invalid interface::view, selector attributes given \
								but top level mod misses `#[interface::with_selector] attribute.`";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							if let Some(ViewAttr::NoSelector) = selector_attr {
								let msg =
									"Invalid interface::view, both `#[interface::no_selector]` and \
								`#[interface::use_selector($ident)]` used on the same method. Use either one or the other";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							if selector_attr.is_some() {
								let msg = "Invalid interface::view, multiple `#[interface::use_selector($ident)]` \
								attributes used on the same method. Only one is allowed.";
								return Err(syn::Error::new(method.sig.span(), msg))
							}

							selector_attr = Some(attr);
						},
					}

					Ok((view_idx_attrs, selector_attr))
				},
			)?;

		if view_idx_attrs.len() != 1 {
			let msg = if view_idx_attrs.is_empty() {
				"Invalid interface::view, requires view_index attribute i.e. `#[interface::view_index(u8)]`"
			} else {
				"Invalid interface::view, too many view_index attributes given"
			};
			return Err(syn::Error::new(method.sig.span(), msg))
		}
		let view_index = match view_idx_attrs.pop().unwrap() {
			ViewAttr::Index(idx) => idx,
			_ => unreachable!("checked during creation of the let binding"),
		};
		if let Some(used_fn) = indices.insert(view_index, method.sig.ident.clone()) {
			let msg = format!(
				"View indices are conflicting: Both functions {} and {} are at index {}",
				used_fn, method.sig.ident, view_index,
			);
			let mut err = syn::Error::new(used_fn.span(), &msg);
			err.combine(syn::Error::new(method.sig.ident.span(), msg));
			return Err(err)
		}

		let with_selector = match selector_attr.as_ref() {
			Some(attr) => match attr {
				ViewAttr::UseSelector(_) => true,
				ViewAttr::NoSelector => false,
				_ => unreachable!("checked during creation of the let binding"),
			},
			None => global_selector,
		};

		// `try_fold()` above ensures that selector attributes are only
		// provided if global selector is et
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
				Some(syn::FnArg::Typed(arg)) => check_view_first_arg_type(&arg.ty)?,
			};

			let selector_ty = match selector_attr {
				Some(attr) => match attr {
					ViewAttr::UseSelector(name) => definition::SelectorType::Named {
						name: name.clone(),
						return_ty: first_arg_ty,
					},
					ViewAttr::NoSelector =>
						unreachable!("checked during creation of the let binding"),
					_ => unreachable!("checked during creation of the let binding"),
				},
				None => definition::SelectorType::Default { return_ty: first_arg_ty },
			};

			(1, Some(selector_ty))
		} else {
			(0, None)
		};

		let output = if let syn::ReturnType::Type(_, ty) = &method.sig.output {
			check_view_return_type(ty)?
		} else {
			let msg = "Invalid Interface::view, require return type \
						Result<$ty, InterfaceError>";
			return Err(syn::Error::new(method.sig.span(), msg))
		};

		// Skip first argument if not selector
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
				let msg = "Invalid interface::view, argument has too many attributes";
				return Err(syn::Error::new(arg.span(), msg))
			}

			let arg_ident = if let syn::Pat::Ident(pat) = &*arg.pat {
				pat.ident.clone()
			} else {
				let msg = "Invalid interface::view, argument must be ident";
				return Err(syn::Error::new(arg.pat.span(), msg))
			};

			let arg_ty = super::adapt_type_to_generic_if_self(arg.ty.clone());

			args.push((!arg_attrs.is_empty(), arg_ident, arg_ty));
		}

		let docs = get_doc_literals(&method.attrs);

		views.views.push(SingleViewDef {
			output,
			selector,
			name: method.sig.ident.clone(),
			view_index,
			args,
			docs,
			attrs: method.attrs.clone(),
			attr_span,
		});

		Ok(views)
	}

	pub fn check_selectors(&self, selectors: &Option<SelectorDef>) -> syn::Result<()> {
		for view in self.views.iter() {
			if let Some(selector) = &view.selector {
				if let Some(selectors) = selectors.as_ref() {
					selectors.check_selector(selector)?;
				} else {
					let msg = format!(
						"Invalid interface::definition, expected a selector of kind `{:?}`, \
						found none. \
						(try adding a correctly annotated selector method to the trait).",
						selector
					);
					return Err(syn::Error::new(view.attr_span, msg))
				}
			}
		}

		Ok(())
	}
}

#[derive(Clone)]
pub struct SingleViewDef {
	/// Signal whether first argument must
	/// be a selector
	pub selector: Option<definition::SelectorType>,
	/// Function name.
	pub name: syn::Ident,
	/// Information on args: `(is_compact, name, type)`
	pub args: Vec<(bool, syn::Ident, Box<syn::Type>)>,
	/// Return type of the view function
	pub output: Box<syn::Type>,
	/// View index of the interface.
	pub view_index: u8,
	/// Docs, used for metadata.
	pub docs: Vec<syn::Lit>,
	/// Attributes annotated at the top of the view function.
	pub attrs: Vec<syn::Attribute>,
	/// The span of the view definition
	pub attr_span: proc_macro2::Span,
}

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(interface);
	syn::custom_keyword!(no_selector);
	syn::custom_keyword!(use_selector);
	syn::custom_keyword!(view_index);
	syn::custom_keyword!(ViewResult);
	syn::custom_keyword!(compact);
	syn::custom_keyword!(Select);
}

/// Parse attributes for item in interface trait definition
/// syntax must be `interface::` (e.g. `#[interface::call]`)
enum ViewAttr {
	Index(u8),
	UseSelector(syn::Ident),
	NoSelector,
}

impl syn::parse::Parse for ViewAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::interface>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::view_index) {
			content.parse::<keyword::view_index>()?;
			let view_index_content;
			syn::parenthesized!(view_index_content in content);
			let index = view_index_content.parse::<syn::LitInt>()?;
			if !index.suffix().is_empty() {
				let msg = "Number literal must not have a suffix";
				return Err(syn::Error::new(index.span(), msg))
			}
			Ok(ViewAttr::Index(index.base10_parse()?))
		} else if lookahead.peek(keyword::use_selector) {
			content.parse::<keyword::use_selector>()?;
			let use_selector_content;
			syn::parenthesized!(use_selector_content in content);
			Ok(ViewAttr::UseSelector(use_selector_content.parse::<syn::Ident>()?))
		} else if lookahead.peek(keyword::no_selector) {
			content.parse::<keyword::no_selector>()?;
			Ok(ViewAttr::NoSelector)
		} else {
			Err(lookahead.error())
		}
	}
}

/// Check the syntax is `Select<$ident>`
pub fn check_view_first_arg_type(ty: &syn::Type) -> syn::Result<Box<syn::Type>> {
	pub struct CheckViewFirstArg(Box<syn::Type>);
	impl syn::parse::Parse for CheckViewFirstArg {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<keyword::Select>()?;
			input.parse::<syn::Token![<]>()?;
			let ty = input.parse::<syn::Type>()?;
			input.parse::<syn::Token![>]>()?;
			Ok(Self(Box::new(ty)))
		}
	}

	let check = syn::parse2::<CheckViewFirstArg>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `Select<$ty>`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(check.0)
}

/// Check the return type is `Result<$type, InterfaceError>`
pub fn check_view_return_type(ty: &syn::Type) -> syn::Result<Box<syn::Type>> {
	pub struct CheckViewReturnType(Box<syn::Type>);
	impl syn::parse::Parse for CheckViewReturnType {
		fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
			input.parse::<keyword::ViewResult>()?;
			input.parse::<syn::Token![<]>()?;
			let ty = input.parse::<syn::Type>()?;
			input.parse::<syn::Token![>]>()?;
			Ok(Self(Box::new(ty)))
		}
	}

	let check = syn::parse2::<CheckViewReturnType>(ty.to_token_stream()).map_err(|e| {
		let msg = "Invalid type: expected `ViewResult<$ident>`";
		let mut err = syn::Error::new(ty.span(), msg);
		err.combine(e);
		err
	})?;

	Ok(check.0)
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
