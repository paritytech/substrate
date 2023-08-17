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

use crate::construct_runtime_v2::Def;
use crate::construct_runtime_v2::parse::pallets::{AllPalletsDeclaration, ExplicitAllPalletsDeclaration};
use syn::{Ident, Result};
use quote::quote;
use proc_macro2::TokenStream as TokenStream2;
use std::collections::HashSet;
use frame_support_procedural_tools::generate_crate_access;
use frame_support_procedural_tools::generate_hidden_includes;
use frame_support_procedural_tools::generate_crate_access_2018;
use std::str::FromStr;
use itertools::Itertools;
use cfg_expr::Predicate;

use crate::construct_runtime::expand;
use crate::construct_runtime::parse::Pallet;

use crate::construct_runtime::decl_all_pallets;
use crate::construct_runtime::decl_pallet_runtime_setup;
use crate::construct_runtime::decl_integrity_test;
use crate::construct_runtime::decl_static_assertions;

/// The fixed name of the system pallet.
const SYSTEM_PALLET_NAME: &str = "System";

pub fn expand(mut def: Def) -> proc_macro2::TokenStream {
    match def.pallets {
        (AllPalletsDeclaration::Implicit(decl), result) => {
            result
        }
        (AllPalletsDeclaration::Explicit(ref decl), ref result) => {
            let res = construct_runtime_final_expansion(def.runtime_struct.ident.clone(), decl.clone());

            let res = res.unwrap_or_else(|e| e.to_compile_error());

            let res = expander::Expander::new("construct_runtime")
                .dry(std::env::var("FRAME_EXPAND").is_err())
                .verbose(true)
                .write_to_out_dir(res)
                .expect("Does not fail because of IO in OUT_DIR; qed");
        
            res.into()
        }
    }
}

fn construct_runtime_final_expansion(
	name: Ident,
	definition: ExplicitAllPalletsDeclaration,
) -> Result<TokenStream2> {
	let ExplicitAllPalletsDeclaration { pallets, pallets_token, .. } = definition;

	let system_pallet =
		pallets.iter().find(|decl| decl.name == SYSTEM_PALLET_NAME).ok_or_else(|| {
			syn::Error::new(
				pallets_token.span.join(),
				"`System` pallet declaration is missing. \
			 Please add this line: `System: frame_system::{Pallet, Call, Storage, Config<T>, Event<T>},`",
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

	let frame_system = generate_crate_access_2018("frame-system")?;
	let block = quote!(<#name as #frame_system::Config>::Block);
	let unchecked_extrinsic = quote!(<#block as #scrate::sp_runtime::traits::Block>::Extrinsic);

	let outer_event =
	expand::expand_outer_enum(&name, &pallets, &scrate, expand::OuterEnumType::Event)?;
	let outer_error =
    expand::expand_outer_enum(&name, &pallets, &scrate, expand::OuterEnumType::Error)?;

	let outer_origin = expand::expand_outer_origin(&name, system_pallet, &pallets, &scrate)?;
	let all_pallets = decl_all_pallets(&name, pallets.iter(), &features);
	let pallet_to_index = decl_pallet_runtime_setup(&name, &pallets, &scrate);

	let dispatch = expand::expand_outer_dispatch(&name, system_pallet, &pallets, &scrate);
	let metadata = expand::expand_runtime_metadata(
		&name,
		&pallets,
		&scrate,
		&unchecked_extrinsic,
		&system_pallet.path,
	);
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

		#outer_error

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
