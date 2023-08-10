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
// limitations under the License

use crate::construct_runtime::parse::ExecutiveSection;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::Result;

pub fn expand_executive(
	runtime: &Ident,
	system: &Ident,
	scrate: &TokenStream,
	block: &TokenStream,
	executive_section: ExecutiveSection,
) -> Result<TokenStream> {
	let executive = generate_crate_access_2018("frame-executive")?;

	let on_runtime_upgrade = match executive_section.custom_on_runtime_upgrade {
		Some(custom) => quote!(Some(#custom)),
		None => quote!(()),
	};

	let try_runtime_section = if let Ok(try_runtime) =
		generate_crate_access_2018("frame-try-runtime")
	{
		quote! {
			#[cfg(feature = "try-runtime")]
			impl #runtime {
				fn api_impl_try_runtime_upgrade(checks: #try_runtime::UpgradeCheckSelect) -> Result<Weight, #scrate::sp_runtime::TryRuntimeError> {
					Executive::try_runtime_upgrade(checks)
				}

				fn api_impl_try_execute_block(
					block: #block,
					state_root_check: bool,
					signature_check: bool,
					select: #try_runtime::TryStateSelect
				) -> Result<Weight, &'static str> {
					Executive::try_execute_block(block, state_root_check, signature_check, select)
				}
			}
		}
	} else {
		quote!()
	};

	let res = quote! {
		/// Executive: handles dispatch to the various modules.
		pub type Executive = #executive::Executive<
			#runtime,
			#block,
			#system::ChainContext<#runtime>,
			#runtime,
			AllPalletsWithSystem,
			#on_runtime_upgrade
		>;

		impl #runtime {
			pub fn api_impl_core_execute_block(block: #block) {
				Executive::execute_block(block);
			}

			pub fn api_impl_core_initialize_block(header: &<#block as #scrate::sp_runtime::traits::Block>::Header) {
				Executive::initialize_block(header);
			}

			pub fn api_impl_builder_apply_extrinsic(extrinsic: <#block as #scrate::sp_runtime::traits::Block>::Extrinsic) ->  #scrate::sp_runtime::ApplyExtrinsicResult {
				Executive::apply_extrinsic(extrinsic)
			}

			pub fn api_impl_builder_finalize_block() -> <#block as #scrate::sp_runtime::traits::Block>::Header {
				Executive::finalize_block()
			}

			pub fn api_impl_validate_transaction(
				source: #scrate::sp_runtime::transaction_validity::TransactionSource,
				tx: <Block as #scrate::sp_runtime::traits::Block>::Extrinsic,
				block_hash: <Block as #scrate::sp_runtime::traits::Block>::Hash,
			) -> #scrate::sp_runtime::transaction_validity::TransactionValidity {
				Executive::validate_transaction(source, tx, block_hash)
			}

			pub fn api_impl_offchain_worker(header: &<Block as #scrate::sp_runtime::traits::Block>::Header) {
				Executive::offchain_worker(header)
			}

			#try_runtime_section
		}
	};

	Ok(res)
}
