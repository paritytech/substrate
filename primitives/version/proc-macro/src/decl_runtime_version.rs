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

use codec::Encode;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
	parse::{Error, Result},
	parse_macro_input,
	spanned::Spanned as _,
	Expr, ExprLit, FieldValue, ItemConst, Lit,
};

/// This macro accepts a `const` item that has a struct initializer expression of `RuntimeVersion`-like type.
/// The macro will pass through this declaration and append an item declaration that will
/// lead to emitting a wasm custom section with the contents of `RuntimeVersion`.
pub fn decl_runtime_version_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let item = parse_macro_input!(input as ItemConst);
	decl_runtime_version_impl_inner(item)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn decl_runtime_version_impl_inner(item: ItemConst) -> Result<TokenStream> {
	let runtime_version = ParseRuntimeVersion::parse_expr(&*item.expr)?.build(item.expr.span())?;
	let link_section =
		generate_emit_link_section_decl(&runtime_version.encode(), "runtime_version");

	Ok(quote! {
		#item
		#link_section
	})
}

/// This is a duplicate of `sp_version::RuntimeVersion`. We cannot unfortunately use the original
/// declaration, because if we directly depend on `sp_version` from this proc-macro cargo will
/// enable `std` feature even for `no_std` wasm runtime builds.
///
/// One difference from the original definition is the `apis` field. Since we don't actually parse
/// `apis` from this macro it will always be emitteed as empty. An empty vector can be encoded as
/// a zero-byte, thus `u8` is sufficient here.
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
			_ =>
				return Err(Error::new(init_expr.span(), "expected a struct initializer expression")),
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
			syn::Member::Unnamed(_) =>
				return Err(Error::new(field_value.span(), "only named members must be used")),
		};

		fn parse_once<T>(
			value: &mut Option<T>,
			field: &FieldValue,
			parser: impl FnOnce(&Expr) -> Result<T>,
		) -> Result<()> {
			if value.is_some() {
				return Err(Error::new(field.span(), "field is already initialized before"))
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
			parse_once(&mut self.authoring_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "spec_version" {
			parse_once(&mut self.spec_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "impl_version" {
			parse_once(&mut self.impl_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "transaction_version" {
			parse_once(&mut self.transaction_version, field_value, Self::parse_num_literal)?;
		} else if field_name == "apis" {
			// Intentionally ignored
			//
			// The definition will pass through for the declaration, however, it won't get into
			// the "runtime_version" custom section. `impl_runtime_apis` is responsible for generating
			// a custom section with the supported runtime apis descriptor.
		} else {
			return Err(Error::new(field_name.span(), "unknown field"))
		}

		Ok(())
	}

	fn parse_num_literal(expr: &Expr) -> Result<u32> {
		let lit = match *expr {
			Expr::Lit(ExprLit { lit: Lit::Int(ref lit), .. }) => lit,
			_ =>
				return Err(Error::new(
					expr.span(),
					"only numeric literals (e.g. `10`) are supported here",
				)),
		};
		lit.base10_parse::<u32>()
	}

	fn parse_str_literal(expr: &Expr) -> Result<String> {
		let mac = match *expr {
			Expr::Macro(syn::ExprMacro { ref mac, .. }) => mac,
			_ => return Err(Error::new(expr.span(), "a macro expression is expected here")),
		};

		let lit: ExprLit = mac.parse_body().map_err(|e| {
			Error::new(
				e.span(),
				format!("a single literal argument is expected, but parsing is failed: {}", e),
			)
		})?;

		match lit.lit {
			Lit::Str(ref lit) => Ok(lit.value()),
			_ => Err(Error::new(lit.span(), "only string literals are supported here")),
		}
	}

	fn build(self, span: Span) -> Result<RuntimeVersion> {
		macro_rules! required {
			($e:expr) => {
				$e.ok_or_else(|| {
					Error::new(span, format!("required field '{}' is missing", stringify!($e)))
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

fn generate_emit_link_section_decl(contents: &[u8], section_name: &str) -> TokenStream {
	let len = contents.len();
	quote! {
		const _: () = {
			#[cfg(not(feature = "std"))]
			#[link_section = #section_name]
			static SECTION_CONTENTS: [u8; #len] = [#(#contents),*];
		};
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::DecodeAll;
	use std::borrow::Cow;

	#[test]
	fn version_can_be_deserialized() {
		let version_bytes = RuntimeVersion {
			spec_name: "hello".to_string(),
			impl_name: "world".to_string(),
			authoring_version: 10,
			spec_version: 265,
			impl_version: 1,
			apis: 0,
			transaction_version: 2,
		}
		.encode();

		assert_eq!(
			sp_version::RuntimeVersion::decode_all(&mut &version_bytes[..]).unwrap(),
			sp_version::RuntimeVersion {
				spec_name: "hello".into(),
				impl_name: "world".into(),
				authoring_version: 10,
				spec_version: 265,
				impl_version: 1,
				apis: Cow::Owned(vec![]),
				transaction_version: 2,
			},
		);
	}
}
