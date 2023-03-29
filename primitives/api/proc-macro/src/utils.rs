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

use proc_macro2::{Span, TokenStream};

use syn::{
	parse_quote, spanned::Spanned, token::And, Attribute, Error, FnArg, GenericArgument, Ident,
	ImplItem, ItemImpl, Pat, Path, PathArguments, Result, ReturnType, Signature, Type, TypePath,
};

use quote::{format_ident, quote};

use proc_macro_crate::{crate_name, FoundCrate};

use crate::common::API_VERSION_ATTRIBUTE;

use inflector::Inflector;

/// Generates the access to the `sc_client` crate.
pub fn generate_crate_access() -> TokenStream {
	match crate_name("sp-api") {
		Ok(FoundCrate::Itself) => quote!(sp_api),
		Ok(FoundCrate::Name(renamed_name)) => {
			let renamed_name = Ident::new(&renamed_name, Span::call_site());
			quote!(#renamed_name)
		},
		Err(e) => {
			let err = Error::new(Span::call_site(), e).to_compile_error();
			quote!( #err )
		},
	}
}

/// Generates the name of the module that contains the trait declaration for the runtime.
pub fn generate_runtime_mod_name_for_trait(trait_: &Ident) -> Ident {
	Ident::new(
		&format!("runtime_decl_for_{}", trait_.to_string().to_snake_case()),
		Span::call_site(),
	)
}

/// Get the type of a `syn::ReturnType`.
pub fn return_type_extract_type(rt: &ReturnType) -> Type {
	match rt {
		ReturnType::Default => parse_quote!(()),
		ReturnType::Type(_, ref ty) => *ty.clone(),
	}
}

/// Replace the `_` (wild card) parameter names in the given signature with unique identifiers.
pub fn replace_wild_card_parameter_names(input: &mut Signature) {
	let mut generated_pattern_counter = 0;
	input.inputs.iter_mut().for_each(|arg| {
		if let FnArg::Typed(arg) = arg {
			arg.pat = Box::new(generate_unique_pattern(
				(*arg.pat).clone(),
				&mut generated_pattern_counter,
			));
		}
	});
}

/// Fold the given `Signature` to make it usable on the client side.
pub fn fold_fn_decl_for_client_side(
	input: &mut Signature,
	block_hash: &TokenStream,
	crate_: &TokenStream,
) {
	replace_wild_card_parameter_names(input);

	// Add `&self, at:& Block::Hash` as parameters to each function at the beginning.
	input.inputs.insert(0, parse_quote!( __runtime_api_at_param__: #block_hash ));
	input.inputs.insert(0, parse_quote!(&self));

	// Wrap the output in a `Result`
	input.output = {
		let ty = return_type_extract_type(&input.output);
		parse_quote!( -> std::result::Result<#ty, #crate_::ApiError> )
	};
}

/// Generate an unique pattern based on the given counter, if the given pattern is a `_`.
pub fn generate_unique_pattern(pat: Pat, counter: &mut u32) -> Pat {
	match pat {
		Pat::Wild(_) => {
			let generated_name =
				Ident::new(&format!("__runtime_api_generated_name_{}__", counter), pat.span());
			*counter += 1;

			parse_quote!( #generated_name )
		},
		_ => pat,
	}
}

/// Allow `&self` in parameters of a method.
pub enum AllowSelfRefInParameters {
	/// Allows `&self` in parameters, but doesn't return it as part of the parameters.
	YesButIgnore,
	No,
}

/// Extracts the name, the type and `&` or ``(if it is a reference or not)
/// for each parameter in the given function signature.
pub fn extract_parameter_names_types_and_borrows(
	sig: &Signature,
	allow_self: AllowSelfRefInParameters,
) -> Result<Vec<(Pat, Type, Option<And>)>> {
	let mut result = Vec::new();
	let mut generated_pattern_counter = 0;
	for input in sig.inputs.iter() {
		match input {
			FnArg::Typed(arg) => {
				let (ty, borrow) = match &*arg.ty {
					Type::Reference(t) => ((*t.elem).clone(), Some(t.and_token)),
					t => (t.clone(), None),
				};

				let name =
					generate_unique_pattern((*arg.pat).clone(), &mut generated_pattern_counter);
				result.push((name, ty, borrow));
			},
			FnArg::Receiver(_) if matches!(allow_self, AllowSelfRefInParameters::No) =>
				return Err(Error::new(input.span(), "`self` parameter not supported!")),
			FnArg::Receiver(recv) =>
				if recv.mutability.is_some() || recv.reference.is_none() {
					return Err(Error::new(recv.span(), "Only `&self` is supported!"))
				},
		}
	}

	Ok(result)
}

/// Prefix the given function with the trait name.
pub fn prefix_function_with_trait<F: ToString>(trait_: &Ident, function: &F) -> String {
	format!("{}_{}", trait_, function.to_string())
}

/// Extract all types that appear in signatures in the given `ImplItem`'s.
///
/// If a type is a reference, the inner type is extracted (without the reference).
pub fn extract_all_signature_types(items: &[ImplItem]) -> Vec<Type> {
	items
		.iter()
		.filter_map(|i| match i {
			ImplItem::Method(method) => Some(&method.sig),
			_ => None,
		})
		.flat_map(|sig| {
			let ret_ty = match &sig.output {
				ReturnType::Default => None,
				ReturnType::Type(_, ty) => Some((**ty).clone()),
			};

			sig.inputs
				.iter()
				.filter_map(|i| match i {
					FnArg::Typed(arg) => Some(&arg.ty),
					_ => None,
				})
				.map(|ty| match &**ty {
					Type::Reference(t) => (*t.elem).clone(),
					_ => (**ty).clone(),
				})
				.chain(ret_ty)
		})
		.collect()
}

/// Extracts the block type from a trait path.
///
/// It is expected that the block type is the first type in the generic arguments.
pub fn extract_block_type_from_trait_path(trait_: &Path) -> Result<&TypePath> {
	let span = trait_.span();
	let generics = trait_
		.segments
		.last()
		.ok_or_else(|| Error::new(span, "Empty path not supported"))?;

	match &generics.arguments {
		PathArguments::AngleBracketed(ref args) => args
			.args
			.first()
			.and_then(|v| match v {
				GenericArgument::Type(Type::Path(ref block)) => Some(block),
				_ => None,
			})
			.ok_or_else(|| Error::new(args.span(), "Missing `Block` generic parameter.")),
		PathArguments::None => {
			let span = trait_.segments.last().as_ref().unwrap().span();
			Err(Error::new(span, "Missing `Block` generic parameter."))
		},
		PathArguments::Parenthesized(_) =>
			Err(Error::new(generics.arguments.span(), "Unexpected parentheses in path!")),
	}
}

/// Should a qualified trait path be required?
///
/// e.g. `path::Trait` is qualified and `Trait` is not.
pub enum RequireQualifiedTraitPath {
	Yes,
	No,
}

/// Extract the trait that is implemented by the given `ItemImpl`.
pub fn extract_impl_trait(impl_: &ItemImpl, require: RequireQualifiedTraitPath) -> Result<&Path> {
	impl_
		.trait_
		.as_ref()
		.map(|v| &v.1)
		.ok_or_else(|| Error::new(impl_.span(), "Only implementation of traits are supported!"))
		.and_then(|p| {
			if p.segments.len() > 1 || matches!(require, RequireQualifiedTraitPath::No) {
				Ok(p)
			} else {
				Err(Error::new(
					p.span(),
					"The implemented trait has to be referenced with a path, \
					e.g. `impl client::Core for Runtime`.",
				))
			}
		})
}

/// Parse the given attribute as `API_VERSION_ATTRIBUTE`.
pub fn parse_runtime_api_version(version: &Attribute) -> Result<u64> {
	let version = version.parse_args::<syn::LitInt>().map_err(|_| {
		Error::new(
			version.span(),
			&format!(
				"Unexpected `{api_version}` attribute. The supported format is `{api_version}(1)`",
				api_version = API_VERSION_ATTRIBUTE
			),
		)
	})?;

	version.base10_parse()
}

/// Each versioned trait is named 'ApiNameVN' where N is the specific version. E.g. ParachainHostV2
pub fn versioned_trait_name(trait_ident: &Ident, version: u64) -> Ident {
	format_ident!("{}V{}", trait_ident, version)
}

/// Extract the documentation from the provided attributes.
pub fn get_doc_literals(attrs: &[syn::Attribute]) -> Vec<syn::Lit> {
	attrs
		.iter()
		.filter_map(|attr| {
			let Ok(syn::Meta::NameValue(meta)) = attr.parse_meta() else {
				return None
			};

			meta.path.get_ident().filter(|ident| *ident == "doc").map(|_| meta.lit)
		})
		.collect()
}

/// Filters all attributes except the cfg ones.
pub fn filter_cfg_attributes(attrs: &[syn::Attribute]) -> Vec<syn::Attribute> {
	attrs.iter().filter(|a| a.path.is_ident("cfg")).cloned().collect()
}

#[cfg(test)]
mod tests {
	use assert_matches::assert_matches;

	use super::*;

	#[test]
	fn check_get_doc_literals() {
		const FIRST: &'static str = "hello";
		const SECOND: &'static str = "WORLD";

		let doc: Attribute = parse_quote!(#[doc = #FIRST]);
		let doc_world: Attribute = parse_quote!(#[doc = #SECOND]);

		let attrs = vec![
			doc.clone(),
			parse_quote!(#[derive(Debug)]),
			parse_quote!(#[test]),
			parse_quote!(#[allow(non_camel_case_types)]),
			doc_world.clone(),
		];

		let docs = get_doc_literals(&attrs);
		assert_eq!(docs.len(), 2);
		assert_matches!(&docs[0], syn::Lit::Str(val) if val.value() == FIRST);
		assert_matches!(&docs[1], syn::Lit::Str(val) if val.value() == SECOND);
	}

	#[test]
	fn check_filter_cfg_attributes() {
		let cfg_std: Attribute = parse_quote!(#[cfg(feature = "std")]);
		let cfg_benchmarks: Attribute = parse_quote!(#[cfg(feature = "runtime-benchmarks")]);

		let attrs = vec![
			cfg_std.clone(),
			parse_quote!(#[derive(Debug)]),
			parse_quote!(#[test]),
			cfg_benchmarks.clone(),
			parse_quote!(#[allow(non_camel_case_types)]),
		];

		let filtered = filter_cfg_attributes(&attrs);
		assert_eq!(filtered.len(), 2);
		assert_eq!(cfg_std, filtered[0]);
		assert_eq!(cfg_benchmarks, filtered[1]);
	}
}
