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
	unwrap_or_error, generate_crate_access, generate_hidden_includes,
	generate_runtime_mod_name_for_trait, fold_fn_decl_for_client_side
};

use proc_macro;
use proc_macro2::TokenStream;

use quote::quote;

use syn::{
	spanned::Spanned, parse_macro_input, parse::{Parse, ParseStream, Result, Error},
	fold::{self, Fold}, FnDecl, parse_quote, ItemTrait, Generics, GenericParam,
};

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "DECL_RUNTIME_APIS";

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
fn extend_generics_with_block(generics: &mut Generics) -> Result<()> {
	generics.params.iter().try_for_each(|p| match p {
		GenericParam::Type(ty) if &ty.ident.to_string() == "Block" => {
			Err(Error::new(ty.span(), "`Block` generic parameter will be added automatically \
				by the `decl_runtime_apis!` macro!")
			)
		},
		_ => Ok(())
	})?;

	let c = generate_crate_access(HIDDEN_INCLUDES_ID);

	generics.lt_token = Some(parse_quote!(<));
	generics.params.insert(0, parse_quote!( Block: #c::runtime_api::BlockT ));
	generics.gt_token = Some(parse_quote!(>));

	Ok(())
}

/// Generate the decleration of the trait for the runtime.
fn generate_runtime_decls(decls: &[ItemTrait]) -> Result<TokenStream> {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();
		extend_generics_with_block(&mut decl.generics)?;
		let mod_name = generate_runtime_mod_name_for_trait(&decl.ident);

		result.push(quote!(
			#[doc(hidden)]
			pub mod #mod_name {
				use super::*;

				#decl
			}
		));
	}

	Ok(quote!( #( #result )* ))
}

/// Modify the given runtime api declaration to be usable on the client side.
struct ToClientSideDecl<'a> {
	block_id: &'a TokenStream,
	crate_: &'a TokenStream,
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
		// Let's ignore the error here, as it will be generated in `generate_runtime_decl` as well.
		let _ = extend_generics_with_block(&mut input.generics);

		{
			// Add the `Core` runtime api as super trait.
			let crate_ = &self.crate_;
			input.supertraits.push(parse_quote!( #crate_::runtime_api::Core<Block> ));
		}

		fold::fold_item_trait(self, input)
	}
}

/// Generate the decleration of the trait for the client side.
fn generate_client_side_decls(decls: &[ItemTrait]) -> TokenStream {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
		let block_id = quote!( #crate_::runtime_api::BlockId<Block> );
		let mut to_client_side = ToClientSideDecl { crate_: &crate_, block_id: &block_id };

		result.push(to_client_side.fold_item_trait(decl));
	}

	quote!( #( #result )* )
}

/// The implementation of the `decl_runtime_apis!` macro.
pub fn decl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all trait declarations
	let RuntimeApiDecls { decls: api_decls } = parse_macro_input!(input as RuntimeApiDecls);
	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let runtime_decls = unwrap_or_error(generate_runtime_decls(&api_decls));
	let client_side_decls = generate_client_side_decls(&api_decls);

	quote!(
		#hidden_includes

		#runtime_decls

		#client_side_decls
	).into()
}
