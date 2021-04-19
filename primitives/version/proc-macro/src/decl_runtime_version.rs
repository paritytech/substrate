// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::utils::{generate_crate_access, generate_hidden_includes};
use std::mem;
use codec::Encode;
use syn::{
	Expr, ExprLit, ExprStruct, FieldValue, ItemConst, Lit,
	parse::{Result, Error},
	parse_macro_input,
	spanned::Spanned as _,
};
use quote::quote;
use proc_macro2::{TokenStream, Span};

#[derive(Encode)]
struct RuntimeVersion {
	spec_name: String,
	impl_name: String,
	authoring_version: u32,
	spec_version: u32,
	impl_version: u32,
	apis: u8,
	transaction_version: u32,
}

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "DECL_RUNTIME_VERSION";

/// This macro accepts a `const` item that has a struct initializer expression of `RuntimeVersion`-like type.
/// The macro will pass through this declaration and append an item declaration that will
/// lead to emitting a wasm custom section with the contents of `RuntimeVersion`.
pub fn decl_runtime_version_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let item = parse_macro_input!(input as ItemConst);
	decl_runtime_version_impl_inner(item)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn decl_runtime_version_impl_inner(mut item: ItemConst) -> Result<TokenStream> {
	let runtime_version = ParseRuntimeVersion::parse_expr(&*item.expr)?.build(item.expr.span())?;

	patch_runtime_str_literal(&mut item);

	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let link_section = generate_emit_link_section_decl(&runtime_version.encode(), "runtime_version");

	Ok(quote! {
		#hidden_includes
		#item
		#link_section
	})
}

#[derive(Default, Debug)]
struct ParseRuntimeVersion {
	spec_name: Option<String>,
	impl_name: Option<String>,
	authoring_version: Option<u32>,
	spec_version: Option<u32>,
	impl_version: Option<u32>,
	transaction_version: Option<u32>,
}

impl ParseRuntimeVersion {
	fn parse_expr(init_expr: &Expr) -> Result<ParseRuntimeVersion> {
		let init_expr = match init_expr {
			Expr::Struct(ref e) => e,
			_ => {
				return Err(Error::new(
					init_expr.span(),
					"expected a struct initializer expression",
				))
			}
		};

		let mut parsed = ParseRuntimeVersion::default();
		for field_value in init_expr.fields.iter() {
			parsed.parse_field_value(field_value)?;
		}
		Ok(parsed)
	}

	fn parse_field_value(&mut self, field_value: &FieldValue) -> Result<()> {
		let field_name = match field_value.member {
			syn::Member::Named(ref ident) => ident,
			syn::Member::Unnamed(_) => {
				return Err(Error::new(
					field_value.span(),
					"only named members must be used",
				));
			}
		};

		fn parse_once<T>(
			value: &mut Option<T>,
			field: &FieldValue,
			parser: impl FnOnce(&Expr) -> Result<T>,
		) -> Result<()> {
			if value.is_some() {
				return Err(Error::new(
					field.span(),
					"field is already initialized before",
				));
			} else {
				*value = Some(parser(&field.expr)?);
				Ok(())
			}
		}

		if field_name == "spec_name" {
			parse_once(&mut self.spec_name, field_value, Self::parse_str_literal)?;
		} else if field_name == "impl_name" {
			parse_once(&mut self.impl_name, field_value, Self::parse_str_literal)?;
		} else if field_name == "authoring_version" {
			parse_once(
				&mut self.authoring_version,
				field_value,
				Self::parse_num_literal,
			)?;
		} else if field_name == "spec_version" {
			parse_once(&mut self.spec_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "impl_version" {
			parse_once(&mut self.impl_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "transaction_version" {
			parse_once(
				&mut self.transaction_version,
				field_value,
				Self::parse_num_literal,
			)?;
		} else {
			return Err(Error::new(field_name.span(), "unknown field"));
		}

		Ok(())
	}

	fn parse_num_literal(expr: &Expr) -> Result<u32> {
		let lit = match *expr {
			Expr::Lit(ExprLit {
				lit: Lit::Int(ref lit),
				..
			}) => lit,
			_ => {
				return Err(Error::new(
					expr.span(),
					"only numeric literals (e.g. `10`) are supported here",
				));
			}
		};
		lit.base10_parse::<u32>()
	}

	fn parse_str_literal(expr: &Expr) -> Result<String> {
		let lit = match *expr {
			Expr::Lit(ExprLit {
				lit: Lit::Str(ref lit),
				..
			}) => lit,
			_ => {
				return Err(Error::new(
					expr.span(),
					"only string literals are supported here",
				));
			}
		};
		Ok(lit.value())
	}

	fn build(self, span: Span) -> Result<RuntimeVersion> {
		macro_rules! required {
			($e:expr) => {
				$e.ok_or_else(|| {
					Error::new(
						span,
						format!("required field '{}' is missing", stringify!($e)),
					)
				})?
			};
		}

		let Self {
			spec_name,
			impl_name,
			authoring_version,
			spec_version,
			impl_version,
			transaction_version,
		} = self;

		Ok(RuntimeVersion {
			spec_name: required!(spec_name),
			impl_name: required!(impl_name),
			authoring_version: required!(authoring_version),
			spec_version: required!(spec_version),
			impl_version: required!(impl_version),
			transaction_version: required!(transaction_version),
			apis: 0,
		})
	}
}

/// The macro accepts plain literals for e.g. spec name and impl name. However, the actual definition
/// of `RuntimeVersion` is based on `RuntimeString`.
///
/// This function patches string literals, so that they are wrapped in `RuntimeString::Borrowed`
/// under the hood.
fn patch_runtime_str_literal(item: &mut ItemConst) {
	let init_expr = match &mut *item.expr {
		Expr::Struct(ref mut e) => e,
		_ => panic!(
			"parse stage returns an error if this is not a struct; this won't be reached; qed",
		),
	};

	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	for field_value in init_expr.fields.iter_mut() {
		let field_name = match field_value.member {
			syn::Member::Named(ref ident) => ident,
			syn::Member::Unnamed(_) => {
				panic!(
					"parse stage accepts only named field; this won't be reached; qed",
				);
			}
		};

		if field_name == "impl_name" || field_name == "spec_name" {
			let lit_str_expr = mem::replace(&mut field_value.expr, Expr::Verbatim(TokenStream::new()));

			use syn::parse::Parse;

			let create_runtime_str: syn::ExprMacro = syn::parse_quote! {
				#crate_::create_runtime_str!(#lit_str_expr)
			};

			field_value.expr = Expr::Macro(create_runtime_str);
		}
	}

	// TODO: Rename and update the rustdoc to accomodate the change below

	// Inject the `apis` field.
	let apis_field: syn::FieldValue = syn::parse_quote! {
		apis: #crate_::create_apis_vec!([])
	};
	init_expr.fields.push(apis_field);
}

fn generate_emit_link_section_decl(contents: &[u8], section_name: &str) -> TokenStream {
	let len = contents.len();
	quote! {
		const _: () = {
			#[link_section = #section_name]
			static SECTION_CONTENTS: [u8; #len] = [#(#contents),*];
		};
	}
}
