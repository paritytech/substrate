// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Implementation of `construct_runtime`.
//!
//! `construct_runtime` implementation is recursive and can generate code which will call itself in
//! order to get all the pallet parts for each pallet.
//!
//! Pallets define their parts (`Call`, `Storage`, ..) either explicitly with the syntax
//! `::{Call, ...}` or implicitly.
//!
//! In case a pallet define their part implicitly, then the pallet must provide the macro
//! `construct_runtime_parts`. `construct_rutime` will generate some code which calls the macro
//! `construct_runtime_parts` of the pallet. The `construct_runtime_parts` will generate some code
//! which calls `construct_runtime` again with this time all explicit definition of parts.
//!
//! E.g.
//! ```ignore
//! construct_runtime!(
//! 	...
//! 	{
//! 		System: frame_system = 0, // Implicit definition of parts
//! 		Balance: frame_balance = 1, // Implicit definition of parts
//! 	}
//! );
//! ```
//! This call has some implicit pallet parts, thus it will expand to:
//! ```ignore
//! frame_balance::construct_runtime_parts!(
//! 	// First *argument* is the path to frame_support crate.
//! 	{ frame_support }
//! 	// Second *argument* is the token idenfiying the pallet on which `construct_runtime_parts`
//! 	// must add the parts.
//! 	{ Balance: frame_balance }
//! 	// The other tokens are the tokens in which the parts must be added and once the parts are
//! 	// added it is the tokens the expand into.
//! 	frame_system::construct_runtime_parts!(
//! 		{ frame_support }
//! 		{ System: frame_system }
//! 		construct_runtime!(
//! 			...
//! 			{
//! 				System: frame_system = 0, // Implicit definition of parts
//! 				Balance: frame_balance = 1, // Implicit definition of parts
//! 			}
//! 		);
//! 	);
//! );
//! ```
//! `construct_runtime_parts` must be define add the pallet parts inside some tokens and then
//! expand to those tokens with the parts added.
//! Thus `frame_balance::construct_runtime_parts` must expand to:
//! ```ignore
//! frame_system::construct_runtime_parts!(
//! 	{ frame_support }
//! 	{ System: frame_system }
//! 	construct_runtime!(
//! 		...
//! 		{
//! 			System: frame_system = 0, // Implicit definition of parts
//! 			Balance: frame_balance::{Pallet, Call} = 1, // Explicit definition of parts
//! 		}
//! 	);
//! );
//! ```
//! Then `frame_system::construct_runtime_parts` must expand to:
//! ```ignore
//! construct_runtime!(
//! 	...
//! 	{
//! 		System: frame_system::{Pallet, Call} = 0, // Explicit definition of parts
//! 		Balance: frame_balance::{Pallet, Call} = 1, // Explicit definition of parts
//! 	}
//! );
//! ```
//! This call has no implicit pallet parts, thus it will expand to the runtime construction:
//! ```ignore
//! pub struct Runtime { ... }
//! pub struct Call { ... }
//! impl Call ...
//! pub enum Origin { ... }
//! ...
//! ```

mod expand;
mod parse;

use frame_support_procedural_tools::{
	generate_crate_access, generate_crate_access_2018, generate_hidden_includes,
};
use parse::{
	ExplicitRuntimeDeclaration, ImplicitRuntimeDeclaration, Pallet, RuntimeDeclaration,
	WhereSection,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{Ident, Result};

/// The fixed name of the system pallet.
const SYSTEM_PALLET_NAME: &str = "System";

/// Implementation of `construct_runtime` macro. Either expand to some code which will call
/// `construct_runtime` again, or expand to the final runtime definition.
pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let input_copy = input.clone();
	let definition = syn::parse_macro_input!(input as RuntimeDeclaration);

	let res = match definition {
		RuntimeDeclaration::Implicit(implicit_def) =>
			construct_runtime_intermediary_expansion(input_copy.into(), implicit_def),
		RuntimeDeclaration::Explicit(explicit_decl) =>
			construct_runtime_final_expansion(explicit_decl),
	};

	res.unwrap_or_else(|e| e.to_compile_error()).into()
}

/// When some pallet have implicit parts definition then the macro will expand into a macro call to
/// `construct_runtime_args` of each pallets, see root documentation.
fn construct_runtime_intermediary_expansion(
	input: TokenStream2,
	definition: ImplicitRuntimeDeclaration,
) -> Result<TokenStream2> {
	let frame_support = generate_crate_access_2018("frame-support")?;
	let mut expansion = quote::quote!(
		#frame_support::construct_runtime! { #input }
	);
	for pallet in definition.pallets.iter().filter(|pallet| pallet.pallet_parts.is_none()) {
		let pallet_path = &pallet.path;
		let pallet_name = &pallet.name;
		let pallet_instance = pallet.instance.as_ref().map(|instance| quote::quote!(::<#instance>));
		expansion = quote::quote!(
			#pallet_path::construct_runtime_parts! {
				{ #frame_support }
				{ #pallet_name: #pallet_path #pallet_instance }
				#expansion
			}
		);
	}

	Ok(expansion.into())
}

/// All pallets have explicit definition of parts, this will expand to the runtime declaration.
fn construct_runtime_final_expansion(
	definition: ExplicitRuntimeDeclaration,
) -> Result<TokenStream2> {
	let ExplicitRuntimeDeclaration {
		name,
		where_section: WhereSection { block, node_block, unchecked_extrinsic },
		pallets,
		pallets_token,
	} = definition;

	let hidden_crate_name = "construct_runtime";
	let scrate = generate_crate_access(&hidden_crate_name, "frame-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "frame-support");

	let outer_event = expand::expand_outer_event(&name, &pallets, &scrate)?;

	let outer_origin = expand::expand_outer_origin(&name, &pallets, pallets_token, &scrate)?;
	let all_pallets = decl_all_pallets(&name, pallets.iter());
	let pallet_to_index = decl_pallet_runtime_setup(&pallets, &scrate);

	let dispatch = expand::expand_outer_dispatch(&name, &pallets, &scrate);
	let metadata = expand::expand_runtime_metadata(&name, &pallets, &scrate, &unchecked_extrinsic);
	let outer_config = expand::expand_outer_config(&name, &pallets, &scrate);
	let inherent =
		expand::expand_outer_inherent(&name, &block, &unchecked_extrinsic, &pallets, &scrate);
	let validate_unsigned = expand::expand_outer_validate_unsigned(&name, &pallets, &scrate);
	let integrity_test = decl_integrity_test(&scrate);

	let res = quote!(
		#scrate_decl

		// Prevent UncheckedExtrinsic to print unused warning.
		const _: () = {
			#[allow(unused)]
			type __hidden_use_of_unchecked_extrinsic = #unchecked_extrinsic;
		};

		#[derive(Clone, Copy, PartialEq, Eq, #scrate::sp_runtime::RuntimeDebug)]
		pub struct #name;
		impl #scrate::sp_runtime::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl #scrate::sp_runtime::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}

		#outer_event

		#outer_origin

		#all_pallets

		#pallet_to_index

		#dispatch

		#metadata

		#outer_config

		#inherent

		#validate_unsigned

		#integrity_test
	);

	Ok(res)
}

fn decl_all_pallets<'a>(
	runtime: &'a Ident,
	pallet_declarations: impl Iterator<Item = &'a Pallet>,
) -> TokenStream2 {
	let mut types = TokenStream2::new();
	let mut names = Vec::new();
	for pallet_declaration in pallet_declarations {
		let type_name = &pallet_declaration.name;
		let pallet = &pallet_declaration.path;
		let mut generics = vec![quote!(#runtime)];
		generics.extend(pallet_declaration.instance.iter().map(|name| quote!(#pallet::#name)));
		let type_decl = quote!(
			pub type #type_name = #pallet::Pallet <#(#generics),*>;
		);
		types.extend(type_decl);
		names.push(&pallet_declaration.name);
	}
	// Make nested tuple structure like (((Babe, Consensus), Grandpa), ...)
	// But ignore the system pallet.
	let all_pallets = names
		.iter()
		.filter(|n| **n != SYSTEM_PALLET_NAME)
		.fold(TokenStream2::default(), |combined, name| quote!((#name, #combined)));

	let all_pallets_with_system = names
		.iter()
		.fold(TokenStream2::default(), |combined, name| quote!((#name, #combined)));

	quote!(
		#types
		/// All pallets included in the runtime as a nested tuple of types.
		/// Excludes the System pallet.
		pub type AllPallets = ( #all_pallets );
		/// All pallets included in the runtime as a nested tuple of types.
		pub type AllPalletsWithSystem = ( #all_pallets_with_system );

		/// All modules included in the runtime as a nested tuple of types.
		/// Excludes the System pallet.
		#[deprecated(note = "use `AllPallets` instead")]
		#[allow(dead_code)]
		pub type AllModules = ( #all_pallets );
		/// All modules included in the runtime as a nested tuple of types.
		#[deprecated(note = "use `AllPalletsWithSystem` instead")]
		#[allow(dead_code)]
		pub type AllModulesWithSystem = ( #all_pallets_with_system );
	)
}

fn decl_pallet_runtime_setup(
	pallet_declarations: &[Pallet],
	scrate: &TokenStream2,
) -> TokenStream2 {
	let names = pallet_declarations.iter().map(|d| &d.name);
	let names2 = pallet_declarations.iter().map(|d| &d.name);
	let name_strings = pallet_declarations.iter().map(|d| d.name.to_string());
	let indices = pallet_declarations.iter().map(|pallet| pallet.index as usize);

	quote!(
		/// Provides an implementation of `PalletInfo` to provide information
		/// about the pallet setup in the runtime.
		pub struct PalletInfo;

		impl #scrate::traits::PalletInfo for PalletInfo {
			fn index<P: 'static>() -> Option<usize> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#indices)
					}
				)*

				None
			}

			fn name<P: 'static>() -> Option<&'static str> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					if type_id == #scrate::sp_std::any::TypeId::of::<#names2>() {
						return Some(#name_strings)
					}
				)*

				None
			}
		}
	)
}

fn decl_integrity_test(scrate: &TokenStream2) -> TokenStream2 {
	quote!(
		#[cfg(test)]
		mod __construct_runtime_integrity_test {
			use super::*;

			#[test]
			pub fn runtime_integrity_tests() {
				<AllPalletsWithSystem as #scrate::traits::IntegrityTest>::integrity_test();
			}
		}
	)
}
