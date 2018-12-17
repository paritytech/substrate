// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use utils::{
	generate_crate_access, generate_hidden_includes, generate_runtime_mod_name_for_trait,
	fold_fn_decl_for_client_side, unwrap_or_error
};

use proc_macro;
use proc_macro2::TokenStream;

use quote::quote;

use syn::{
	spanned::Spanned, parse_macro_input, parse::{Parse, ParseStream, Result, Error},
	fold::{self, Fold}, FnDecl, parse_quote, ItemTrait, Generics, GenericParam, Attribute,
	visit::{Visit, self}, FnArg, Pat, TraitBound, Meta, NestedMeta, Lit,
};

use std::collections::HashMap;

use blake2_rfc;

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "DECL_RUNTIME_APIS";

/// The `core_trait` attribute.
const CORE_TRAIT_ATTRIBUTE: &str = "core_trait";
/// The `api_version` attribute.
const API_VERSION_ATTRIBUTE: &str = "api_version";
/// All attributes that we support in the declaratio of a runtime api trait.
const SUPPORTED_ATTRIBUTE_NAMES: &[&str] = &[CORE_TRAIT_ATTRIBUTE, API_VERSION_ATTRIBUTE];

/// The structure used for parsing the runtime api declarations.
struct RuntimeApiDecls {
	decls: Vec<ItemTrait>,
}

impl Parse for RuntimeApiDecls {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut decls = Vec::new();

		while !input.is_empty() {
			decls.push(ItemTrait::parse(input)?);
		}

		Ok(Self { decls })
	}
}

/// Extend the given generics with `Block: BlockT` as first generic parameter.
fn extend_generics_with_block(generics: &mut Generics) {
	let c = generate_crate_access(HIDDEN_INCLUDES_ID);

	generics.lt_token = Some(parse_quote!(<));
	generics.params.insert(0, parse_quote!( Block: #c::runtime_api::BlockT ));
	generics.gt_token = Some(parse_quote!(>));
}

/// Remove all attributes from the vector that are supported by us in the declaration of a runtime
/// api trait. The returned hashmap contains all found attribute names as keys and the rest of the
/// attribute body as `TokenStream`.
fn remove_supported_attributes(attrs: &mut Vec<Attribute>) -> HashMap<&'static str, Attribute> {
	let mut result = HashMap::new();
	attrs.retain(|v| {
		match SUPPORTED_ATTRIBUTE_NAMES.iter().filter(|a| v.path.is_ident(a)).next() {
			Some(attribute) => {
				result.insert(*attribute, v.clone());
				false
			},
			None => true,
		}
	});

	result
}

/// Generate the decleration of the trait for the runtime.
fn generate_runtime_decls(decls: &[ItemTrait]) -> TokenStream {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();
		extend_generics_with_block(&mut decl.generics);
		let mod_name = generate_runtime_mod_name_for_trait(&decl.ident);
		let found_attributes = remove_supported_attributes(&mut decl.attrs);
		let api_version = unwrap_or_error(get_api_version(&found_attributes).map(|v| {
			generate_runtime_api_version(v as u32)
		}));
		let id = generate_runtime_api_id(&decl.ident.to_string());

		result.push(quote!(
			#[doc(hidden)]
			pub mod #mod_name {
				use super::*;

				#decl

				pub #api_version

				pub #id
			}
		));
	}

	quote!( #( #result )* )
}

/// Modify the given runtime api declaration to be usable on the client side.
struct ToClientSideDecl<'a> {
	block_id: &'a TokenStream,
	crate_: &'a TokenStream,
	found_attributes: &'a mut HashMap<&'static str, Attribute>,
}

impl<'a> Fold for ToClientSideDecl<'a> {
	fn fold_fn_decl(&mut self, input: FnDecl) -> FnDecl {
		let input = fold_fn_decl_for_client_side(
			input,
			&self.block_id,
			&self.crate_
		);

		fold::fold_fn_decl(self, input)
	}

	fn fold_item_trait(&mut self, mut input: ItemTrait) -> ItemTrait {
		extend_generics_with_block(&mut input.generics);

		*self.found_attributes = remove_supported_attributes(&mut input.attrs);
		// Check if this is the `Core` runtime api trait.
		let is_core_trait = self.found_attributes.contains_key(CORE_TRAIT_ATTRIBUTE);

		if is_core_trait {
			// Add all the supertraits we want to have for `Core`.
			let crate_ = &self.crate_;
			input.supertraits = parse_quote!(
				'static
				+ Send
				+ Sync
				+ #crate_::runtime_api::ApiExt<Block>
			);
		} else {
			// Add the `Core` runtime api as super trait.
			let crate_ = &self.crate_;
			input.supertraits.push(parse_quote!( #crate_::runtime_api::Core<Block> ));
		}

		// The client side trait is only required when compiling with the feature `std` or `test`.
		input.attrs.push(parse_quote!( #[cfg(any(feature = "std", test))] ));

		fold::fold_item_trait(self, input)
	}
}

/// Parse the given attribute as `API_VERSION_ATTRIBUTE`.
fn parse_runtime_api_version(version: &Attribute) -> Result<u64> {
	let meta = version.parse_meta()?;

	let err = Err(Error::new(
			meta.span(),
			&format!(
				"Unexpected `{api_version}` attribute. The supported format is `{api_version}(1)`",
				api_version = API_VERSION_ATTRIBUTE
			)
		)
	);

	match meta {
		Meta::List(list) => {
			if list.nested.len() > 1 && list.nested.is_empty() {
				err
			} else {
				match list.nested.first().as_ref().map(|v| v.value()) {
					Some(NestedMeta::Literal(Lit::Int(i))) => {
						Ok(i.value())
					},
					_ => err,
				}
			}
		},
		_ => err,
	}
}

/// Generates the identifier as const variable for the given `trait_name`
/// by hashing the `trait_name`.
fn generate_runtime_api_id(trait_name: &str) -> TokenStream {
	let mut res = [0; 8];
	res.copy_from_slice(blake2_rfc::blake2b::blake2b(8, &[], trait_name.as_bytes()).as_bytes());

	quote!(	const ID: [u8; 8] = [ #( #res ),* ]; )
}

/// Generates the const variable that holds the runtime api version.
fn generate_runtime_api_version(version: u32) -> TokenStream {
	quote!( const VERSION: u32 = #version; )
}

/// Generates the implementation of `RuntimeApiInfo` for the given trait.
fn generate_runtime_info_impl(trait_: &ItemTrait, version: u64) -> TokenStream {
	let trait_name = &trait_.ident;
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
	let id = generate_runtime_api_id(&trait_name.to_string());
	let version = generate_runtime_api_version(version as u32);
	let (impl_generics, ty_generics, where_clause) = trait_.generics.split_for_impl();

	quote!(
		 #[cfg(any(feature = "std", test))]
		impl #impl_generics #crate_::runtime_api::RuntimeApiInfo
			for #trait_name #ty_generics #where_clause
		{
			#id
			#version
		}
	)
}

/// Get the api version from the user given attribute or `Ok(1)`, if no attribute was given.
fn get_api_version(found_attributes: &HashMap<&'static str, Attribute>) -> Result<u64> {
	match found_attributes.get(&API_VERSION_ATTRIBUTE) {
		Some(attr) => parse_runtime_api_version(attr),
		None => Ok(1),
	}
}

/// Generate the decleration of the trait for the client side.
fn generate_client_side_decls(decls: &[ItemTrait]) -> TokenStream {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
		let block_id = quote!( #crate_::runtime_api::BlockId<Block> );
		let mut found_attributes = HashMap::new();

		let decl = {
			let mut to_client_side = ToClientSideDecl {
				crate_: &crate_,
				block_id: &block_id,
				found_attributes: &mut found_attributes
			};
			to_client_side.fold_item_trait(decl)
		};

		let api_version = get_api_version(&found_attributes);

		let runtime_info = unwrap_or_error(
			api_version.map(|v| generate_runtime_info_impl(&decl, v))
		);

		result.push(quote!( #decl #runtime_info ));
	}

	quote!( #( #result )* )
}

/// Checks that a trait declaration is in the format we expect.
struct CheckTraitDecl {
	errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for CheckTraitDecl {
	fn visit_fn_arg(&mut self, input: &'ast FnArg) {
		match input {
			FnArg::Captured(ref arg) => {
				match arg.pat {
					Pat::Ident(ref pat) if pat.ident == "at" => {
						self.errors.push(
							Error::new(
								pat.span(),
								"`decl_runtime_apis!` adds automatically a parameter \
								`at: &BlockId<Block>`. Please rename/remove your parameter."
							)
						)
					},
					_ => {}
				}
			},
			FnArg::SelfRef(_) | FnArg::SelfValue(_) => {
				self.errors.push(Error::new(input.span(), "Self values are not supported."))
			}
			_ => {
				self.errors.push(
					Error::new(
						input.span(),
						"Only function arguments in the form `pat: type` are supported."
					)
				)
			}
		}

		visit::visit_fn_arg(self, input);
	}

	fn visit_generic_param(&mut self, input: &'ast GenericParam) {
		match input {
			GenericParam::Type(ty) if &ty.ident == "Block" => {
				self.errors.push(
					Error::new(
						input.span(),
						"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro!"
					)
				)
			},
			_ => {}
		}

		visit::visit_generic_param(self, input);
	}

	fn visit_trait_bound(&mut self, input: &'ast TraitBound) {
		if let Some(last_ident) = input.path.segments.last().map(|v| &v.value().ident) {
			if last_ident == "BlockT" || last_ident == "Block" {
				self.errors.push(
					Error::new(
						input.span(),
						"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro! If you try to use a different trait than the \
						substrate `Block` trait, please rename it locally."
					)
				)
			}
		}

		visit::visit_trait_bound(self, input)
	}
}

/// Check that the trait declarations are in the format we expect.
fn check_trait_decls(decls: &[ItemTrait]) -> Option<TokenStream> {
	let mut checker = CheckTraitDecl { errors: Vec::new() };
	decls.iter().for_each(|decl| visit::visit_item_trait(&mut checker, &decl));

	if checker.errors.is_empty() {
		None
	} else {
		let errors = checker.errors.into_iter().map(|e| e.to_compile_error());
		Some(quote!( #( #errors )* ))
	}
}

/// The implementation of the `decl_runtime_apis!` macro.
pub fn decl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all trait declarations
	let RuntimeApiDecls { decls: api_decls } = parse_macro_input!(input as RuntimeApiDecls);

	if let Some(errors) = check_trait_decls(&api_decls) {
		return errors.into();
	}

	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let runtime_decls = generate_runtime_decls(&api_decls);
	let client_side_decls = generate_client_side_decls(&api_decls);

	quote!(
		#hidden_includes

		#runtime_decls

		#client_side_decls
	).into()
}
