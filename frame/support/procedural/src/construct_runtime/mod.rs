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

//! Implementation of `construct_runtime`.
//!
//! `construct_runtime` implementation is recursive and can generate code which will call itself in
//! order to get all the pallet parts for each pallet.
//!
//! Pallets define their parts (`Call`, `Storage`, ..) either explicitly with the syntax
//! `::{Call, ...}` or implicitly.
//!
//! In case a pallet defines its parts implicitly, then the pallet must provide the
//! `tt_default_parts` macro. `construct_rutime` will generate some code which utilizes `tt_call`
//! to call the `tt_default_parts` macro of the pallet. `tt_default_parts` will then return the
//! default pallet parts as input tokens to the `match_and_replace` macro, which ultimately
//! generates a call to `construct_runtime` again, this time with all the pallet parts explicitly
//! defined.
//!
//! E.g.
//! ```ignore
//! construct_runtime!(
//! 	//...
//! 	{
//! 		System: frame_system = 0, // Implicit definition of parts
//! 		Balances: pallet_balances = 1, // Implicit definition of parts
//! 	}
//! );
//! ```
//! This call has some implicit pallet parts, thus it will expand to:
//! ```ignore
//! frame_support::tt_call! {
//! 	macro = [{ pallet_balances::tt_default_parts }]
//! 	~~> frame_support::match_and_insert! {
//! 		target = [{
//! 			frame_support::tt_call! {
//! 				macro = [{ frame_system::tt_default_parts }]
//! 				~~> frame_support::match_and_insert! {
//! 					target = [{
//! 						construct_runtime!(
//! 							//...
//! 							{
//! 								System: frame_system = 0,
//! 								Balances: pallet_balances = 1,
//! 							}
//! 						);
//! 					}]
//! 					pattern = [{ System: frame_system }]
//! 				}
//! 			}
//! 		}]
//! 		pattern = [{ Balances: pallet_balances }]
//! 	}
//! }
//! ```
//! `tt_default_parts` must be defined. It returns the pallet parts inside some tokens, and
//! then `tt_call` will pipe the returned pallet parts into the input of `match_and_insert`.
//! Thus `match_and_insert` will initially receive the following inputs:
//! ```ignore
//! frame_support::match_and_insert! {
//! 	target = [{
//! 		frame_support::match_and_insert! {
//! 			target = [{
//! 				construct_runtime!(
//! 					//...
//! 					{
//! 						System: frame_system = 0,
//! 						Balances: pallet_balances = 1,
//! 					}
//! 				)
//! 			}]
//! 			pattern = [{ System: frame_system }]
//! 			tokens = [{ ::{Pallet, Call} }]
//! 		}
//! 	}]
//! 	pattern = [{ Balances: pallet_balances }]
//! 	tokens = [{ ::{Pallet, Call} }]
//! }
//! ```
//! After dealing with `pallet_balances`, the inner `match_and_insert` will expand to:
//! ```ignore
//! frame_support::match_and_insert! {
//! 	target = [{
//! 		construct_runtime!(
//! 			//...
//! 			{
//! 				System: frame_system = 0, // Implicit definition of parts
//! 				Balances: pallet_balances::{Pallet, Call} = 1, // Explicit definition of parts
//! 			}
//! 		)
//! 	}]
//! 	pattern = [{ System: frame_system }]
//! 	tokens = [{ ::{Pallet, Call} }]
//! }
//! ```
//! Which will then finally expand to the following:
//! ```ignore
//! construct_runtime!(
//! 	//...
//! 	{
//! 		System: frame_system::{Pallet, Call},
//! 		Balances: pallet_balances::{Pallet, Call},
//! 	}
//! )
//! ```
//! This call has no implicit pallet parts, thus it will expand to the runtime construction:
//! ```ignore
//! pub struct Runtime { ... }
//! pub struct Call { ... }
//! impl Call ...
//! pub enum Origin { ... }
//! ...
//! ```
//!
//! Visualizing the entire flow of `construct_runtime!`, it would look like the following:
//!
//! ```ignore
//! +--------------------+     +---------------------+     +-------------------+
//! |                    |     | (defined in pallet) |     |                   |
//! | construct_runtime! | --> |  tt_default_parts!  | --> | match_and_insert! |
//! | w/ no pallet parts |     |                     |     |                   |
//! +--------------------+     +---------------------+     +-------------------+
//!
//!     +--------------------+
//!     |                    |
//! --> | construct_runtime! |
//!     |  w/ pallet parts   |
//!     +--------------------+
//! ```

mod expand;
mod parse;

use cfg_expr::Predicate;
use frame_support_procedural_tools::{
	generate_crate_access, generate_crate_access_2018, generate_hidden_includes,
};
use itertools::Itertools;
use parse::{
	ExplicitRuntimeDeclaration, ImplicitRuntimeDeclaration, Pallet, RuntimeDeclaration,
	WhereSection,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use std::{collections::HashSet, str::FromStr};
use syn::{spanned::Spanned, Ident, Result};

/// The fixed name of the system pallet.
const SYSTEM_PALLET_NAME: &str = "System";

/// Implementation of `construct_runtime` macro. Either expand to some code which will call
/// `construct_runtime` again, or expand to the final runtime definition.
pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let input_copy = input.clone();
	let definition = syn::parse_macro_input!(input as RuntimeDeclaration);

	let res = match definition {
		RuntimeDeclaration::Implicit(implicit_def) =>
			check_pallet_number(input_copy.clone().into(), implicit_def.pallets.len()).and_then(
				|_| construct_runtime_intermediary_expansion(input_copy.into(), implicit_def),
			),
		RuntimeDeclaration::Explicit(explicit_decl) =>
			check_pallet_number(input_copy.into(), explicit_decl.pallets.len())
				.and_then(|_| construct_runtime_final_expansion(explicit_decl)),
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
			#frame_support::tt_call! {
				macro = [{ #pallet_path::tt_default_parts }]
				frame_support = [{ #frame_support }]
				~~> #frame_support::match_and_insert! {
					target = [{ #expansion }]
					pattern = [{ #pallet_name: #pallet_path #pallet_instance }]
				}
			}
		);
	}

	Ok(expansion)
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

	let system_pallet =
		pallets.iter().find(|decl| decl.name == SYSTEM_PALLET_NAME).ok_or_else(|| {
			syn::Error::new(
				pallets_token.span.join(),
				"`System` pallet declaration is missing. \
			 Please add this line: `System: frame_system::{Pallet, Call, Storage, Config, Event<T>},`",
			)
		})?;
	if !system_pallet.cfg_pattern.is_empty() {
		return Err(syn::Error::new(
			system_pallet.name.span(),
			"`System` pallet declaration is feature gated, please remove any `#[cfg]` attributes",
		))
	}

	let features = pallets
		.iter()
		.filter_map(|decl| {
			(!decl.cfg_pattern.is_empty()).then(|| {
				decl.cfg_pattern.iter().flat_map(|attr| {
					attr.predicates().filter_map(|pred| match pred {
						Predicate::Feature(feat) => Some(feat),
						Predicate::Test => Some("test"),
						_ => None,
					})
				})
			})
		})
		.flatten()
		.collect::<HashSet<_>>();

	let hidden_crate_name = "construct_runtime";
	let scrate = generate_crate_access(hidden_crate_name, "frame-support");
	let scrate_decl = generate_hidden_includes(hidden_crate_name, "frame-support");

	let outer_event = expand::expand_outer_event(&name, &pallets, &scrate)?;

	let outer_origin = expand::expand_outer_origin(&name, system_pallet, &pallets, &scrate)?;
	let all_pallets = decl_all_pallets(&name, pallets.iter(), &features);
	let pallet_to_index = decl_pallet_runtime_setup(&name, &pallets, &scrate);

	let dispatch = expand::expand_outer_dispatch(&name, system_pallet, &pallets, &scrate);
	let metadata = expand::expand_runtime_metadata(&name, &pallets, &scrate, &unchecked_extrinsic);
	let outer_config = expand::expand_outer_config(&name, &pallets, &scrate);
	let inherent =
		expand::expand_outer_inherent(&name, &block, &unchecked_extrinsic, &pallets, &scrate);
	let validate_unsigned = expand::expand_outer_validate_unsigned(&name, &pallets, &scrate);
	let freeze_reason = expand::expand_outer_freeze_reason(&pallets, &scrate);
	let hold_reason = expand::expand_outer_hold_reason(&pallets, &scrate);
	let lock_id = expand::expand_outer_lock_id(&pallets, &scrate);
	let slash_reason = expand::expand_outer_slash_reason(&pallets, &scrate);
	let integrity_test = decl_integrity_test(&scrate);
	let static_assertions = decl_static_assertions(&name, &pallets, &scrate);

	let res = quote!(
		#scrate_decl

		// Prevent UncheckedExtrinsic to print unused warning.
		const _: () = {
			#[allow(unused)]
			type __hidden_use_of_unchecked_extrinsic = #unchecked_extrinsic;
		};

		#[derive(
			Clone, Copy, PartialEq, Eq, #scrate::sp_runtime::RuntimeDebug,
			#scrate::scale_info::TypeInfo
		)]
		pub struct #name;
		impl #scrate::sp_runtime::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl #scrate::sp_runtime::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}

		// Each runtime must expose the `runtime_metadata()` to fetch the runtime API metadata.
		// The function is implemented by calling `impl_runtime_apis!`.
		//
		// However, the `construct_runtime!` may be called without calling `impl_runtime_apis!`.
		// Rely on the `Deref` trait to differentiate between a runtime that implements
		// APIs (by macro impl_runtime_apis!) and a runtime that is simply created (by macro construct_runtime!).
		//
		// Both `InternalConstructRuntime` and `InternalImplRuntimeApis` expose a `runtime_metadata()` function.
		// `InternalConstructRuntime` is implemented by the `construct_runtime!` for Runtime references (`& Runtime`),
		// while `InternalImplRuntimeApis` is implemented by the `impl_runtime_apis!` for Runtime (`Runtime`).
		//
		// Therefore, the `Deref` trait will resolve the `runtime_metadata` from `impl_runtime_apis!`
		// when both macros are called; and will resolve an empty `runtime_metadata` when only the `construct_runtime!`
		// is called.

		#[doc(hidden)]
		trait InternalConstructRuntime {
			#[inline(always)]
			fn runtime_metadata(&self) -> #scrate::sp_std::vec::Vec<#scrate::metadata_ir::RuntimeApiMetadataIR> {
				Default::default()
			}
		}
		#[doc(hidden)]
		impl InternalConstructRuntime for &#name {}

		#outer_event

		#outer_origin

		#all_pallets

		#pallet_to_index

		#dispatch

		#metadata

		#outer_config

		#inherent

		#validate_unsigned

		#freeze_reason

		#hold_reason

		#lock_id

		#slash_reason

		#integrity_test

		#static_assertions
	);

	Ok(res)
}

fn decl_all_pallets<'a>(
	runtime: &'a Ident,
	pallet_declarations: impl Iterator<Item = &'a Pallet>,
	features: &HashSet<&str>,
) -> TokenStream2 {
	let mut types = TokenStream2::new();

	// Every feature set to the pallet names that should be included by this feature set.
	let mut features_to_names = features
		.iter()
		.map(|f| *f)
		.powerset()
		.map(|feat| (HashSet::from_iter(feat), Vec::new()))
		.collect::<Vec<(HashSet<_>, Vec<_>)>>();

	for pallet_declaration in pallet_declarations {
		let type_name = &pallet_declaration.name;
		let pallet = &pallet_declaration.path;
		let mut generics = vec![quote!(#runtime)];
		generics.extend(pallet_declaration.instance.iter().map(|name| quote!(#pallet::#name)));
		let mut attrs = Vec::new();
		for cfg in &pallet_declaration.cfg_pattern {
			let feat = format!("#[cfg({})]\n", cfg.original());
			attrs.extend(TokenStream2::from_str(&feat).expect("was parsed successfully; qed"));
		}
		let type_decl = quote!(
			#(#attrs)*
			pub type #type_name = #pallet::Pallet <#(#generics),*>;
		);
		types.extend(type_decl);

		if pallet_declaration.cfg_pattern.is_empty() {
			for (_, names) in features_to_names.iter_mut() {
				names.push(&pallet_declaration.name);
			}
		} else {
			for (feature_set, names) in &mut features_to_names {
				// Rust tidbit: if we have multiple `#[cfg]` feature on the same item, then the
				// predicates listed in all `#[cfg]` attributes are effectively joined by `and()`,
				// meaning that all of them must match in order to activate the item
				let is_feature_active = pallet_declaration.cfg_pattern.iter().all(|expr| {
					expr.eval(|pred| match pred {
						Predicate::Feature(f) => feature_set.contains(f),
						Predicate::Test => feature_set.contains(&"test"),
						_ => false,
					})
				});

				if is_feature_active {
					names.push(&pallet_declaration.name);
				}
			}
		}
	}

	// All possible features. This will be used below for the empty feature set.
	let mut all_features = features_to_names
		.iter()
		.flat_map(|f| f.0.iter().cloned())
		.collect::<HashSet<_>>();
	let attribute_to_names = features_to_names
		.into_iter()
		.map(|(mut features, names)| {
			// If this is the empty feature set, it needs to be changed to negate all available
			// features. So, we ensure that there is some type declared when all features are not
			// enabled.
			if features.is_empty() {
				let test_cfg = all_features.remove("test").then_some(quote!(test)).into_iter();
				let features = all_features.iter();
				let attr = quote!(#[cfg(all( #(not(#test_cfg)),* #(not(feature = #features)),* ))]);

				(attr, names)
			} else {
				let test_cfg = features.remove("test").then_some(quote!(test)).into_iter();
				let disabled_features = all_features.difference(&features);
				let features = features.iter();
				let attr = quote!(#[cfg(all( #(#test_cfg,)* #(feature = #features,)* #(not(feature = #disabled_features)),* ))]);

				(attr, names)
			}
		})
		.collect::<Vec<_>>();

	let all_pallets_without_system = attribute_to_names.iter().map(|(attr, names)| {
		let names = names.iter().filter(|n| **n != SYSTEM_PALLET_NAME);
		quote! {
			#attr
			/// All pallets included in the runtime as a nested tuple of types.
			/// Excludes the System pallet.
			pub type AllPalletsWithoutSystem = ( #(#names,)* );
		}
	});

	let all_pallets_with_system = attribute_to_names.iter().map(|(attr, names)| {
		quote! {
			#attr
			/// All pallets included in the runtime as a nested tuple of types.
			pub type AllPalletsWithSystem = ( #(#names,)* );
		}
	});

	let all_pallets_without_system_reversed = attribute_to_names.iter().map(|(attr, names)| {
		let names = names.iter().filter(|n| **n != SYSTEM_PALLET_NAME).rev();
		quote! {
			#attr
			/// All pallets included in the runtime as a nested tuple of types in reversed order.
			/// Excludes the System pallet.
			#[deprecated(note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
			pub type AllPalletsWithoutSystemReversed = ( #(#names,)* );
		}
	});

	let all_pallets_with_system_reversed = attribute_to_names.iter().map(|(attr, names)| {
		let names = names.iter().rev();
		quote! {
			#attr
			/// All pallets included in the runtime as a nested tuple of types in reversed order.
			#[deprecated(note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
			pub type AllPalletsWithSystemReversed = ( #(#names,)* );
		}
	});

	let all_pallets_reversed_with_system_first = attribute_to_names.iter().map(|(attr, names)| {
		let system = quote::format_ident!("{}", SYSTEM_PALLET_NAME);
		let names = std::iter::once(&system)
			.chain(names.iter().rev().filter(|n| **n != SYSTEM_PALLET_NAME).cloned());
		quote! {
			#attr
			/// All pallets included in the runtime as a nested tuple of types in reversed order.
			/// With the system pallet first.
			#[deprecated(note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`")]
			pub type AllPalletsReversedWithSystemFirst = ( #(#names,)* );
		}
	});

	quote!(
		#types

		/// All pallets included in the runtime as a nested tuple of types.
		#[deprecated(note = "The type definition has changed from representing all pallets \
			excluding system, in reversed order to become the representation of all pallets \
			including system pallet in regular order. For this reason it is encouraged to use \
			explicitly one of `AllPalletsWithSystem`, `AllPalletsWithoutSystem`, \
			`AllPalletsWithSystemReversed`, `AllPalletsWithoutSystemReversed`. \
			Note that the type `frame_executive::Executive` expects one of `AllPalletsWithSystem` \
			, `AllPalletsWithSystemReversed`, `AllPalletsReversedWithSystemFirst`. More details in \
			https://github.com/paritytech/substrate/pull/10043")]
		pub type AllPallets = AllPalletsWithSystem;

		#( #all_pallets_with_system )*

		#( #all_pallets_without_system )*

		#( #all_pallets_with_system_reversed )*

		#( #all_pallets_without_system_reversed )*

		#( #all_pallets_reversed_with_system_first )*
	)
}

fn decl_pallet_runtime_setup(
	runtime: &Ident,
	pallet_declarations: &[Pallet],
	scrate: &TokenStream2,
) -> TokenStream2 {
	let names = pallet_declarations.iter().map(|d| &d.name).collect::<Vec<_>>();
	let name_strings = pallet_declarations.iter().map(|d| d.name.to_string());
	let module_names = pallet_declarations.iter().map(|d| d.path.module_name());
	let indices = pallet_declarations.iter().map(|pallet| pallet.index as usize);
	let pallet_structs = pallet_declarations
		.iter()
		.map(|pallet| {
			let path = &pallet.path;
			match pallet.instance.as_ref() {
				Some(inst) => quote!(#path::Pallet<#runtime, #path::#inst>),
				None => quote!(#path::Pallet<#runtime>),
			}
		})
		.collect::<Vec<_>>();
	let pallet_attrs = pallet_declarations
		.iter()
		.map(|pallet| {
			pallet.cfg_pattern.iter().fold(TokenStream2::new(), |acc, pattern| {
				let attr = TokenStream2::from_str(&format!("#[cfg({})]", pattern.original()))
					.expect("was successfully parsed before; qed");
				quote! {
					#acc
					#attr
				}
			})
		})
		.collect::<Vec<_>>();

	quote!(
		/// Provides an implementation of `PalletInfo` to provide information
		/// about the pallet setup in the runtime.
		pub struct PalletInfo;

		impl #scrate::traits::PalletInfo for PalletInfo {
			fn index<P: 'static>() -> Option<usize> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					#pallet_attrs
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#indices)
					}
				)*

				None
			}

			fn name<P: 'static>() -> Option<&'static str> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					#pallet_attrs
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#name_strings)
					}
				)*

				None
			}

			fn module_name<P: 'static>() -> Option<&'static str> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					#pallet_attrs
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#module_names)
					}
				)*

				None
			}

			fn crate_version<P: 'static>() -> Option<#scrate::traits::CrateVersion> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					#pallet_attrs
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(
							<#pallet_structs as #scrate::traits::PalletInfoAccess>::crate_version()
						)
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
				#scrate::sp_tracing::try_init_simple();
				<AllPalletsWithSystem as #scrate::traits::IntegrityTest>::integrity_test();
			}
		}
	)
}

fn decl_static_assertions(
	runtime: &Ident,
	pallet_decls: &[Pallet],
	scrate: &TokenStream2,
) -> TokenStream2 {
	let error_encoded_size_check = pallet_decls.iter().map(|decl| {
		let path = &decl.path;
		let assert_message = format!(
			"The maximum encoded size of the error type in the `{}` pallet exceeds \
			`MAX_MODULE_ERROR_ENCODED_SIZE`",
			decl.name,
		);

		quote! {
			#scrate::tt_call! {
				macro = [{ #path::tt_error_token }]
				frame_support = [{ #scrate }]
				~~> #scrate::assert_error_encoded_size! {
					path = [{ #path }]
					runtime = [{ #runtime }]
					assert_message = [{ #assert_message }]
				}
			}
		}
	});

	quote! {
		#(#error_encoded_size_check)*
	}
}

fn check_pallet_number(input: TokenStream2, pallet_num: usize) -> Result<()> {
	let max_pallet_num = {
		if cfg!(feature = "tuples-96") {
			96
		} else if cfg!(feature = "tuples-128") {
			128
		} else {
			64
		}
	};

	if pallet_num > max_pallet_num {
		let no_feature = max_pallet_num == 128;
		return Err(syn::Error::new(
			input.span(),
			format!(
				"{} To increase this limit, enable the tuples-{} feature of [frame_support]. {}",
				"The number of pallets exceeds the maximum number of tuple elements.",
				max_pallet_num + 32,
				if no_feature {
					"If the feature does not exist - it needs to be implemented."
				} else {
					""
				},
			),
		))
	}

	Ok(())
}
