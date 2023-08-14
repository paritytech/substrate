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

use crate::construct_runtime::{parse::PalletPath, Pallet};
use proc_macro2::{Ident, TokenStream};
use quote::quote;

/// Expands aggregate `RuntimeTask` enum.
pub fn expand_outer_task(pallet_decls: &[Pallet], scrate: &TokenStream) -> TokenStream {
	let mut conversion_fns = Vec::new();
	let mut task_variants = Vec::new();
	for decl in pallet_decls {
		if let Some(_) = decl.find_part("Task") {
			let variant_name = &decl.name;
			let path = &decl.path;
			let index = decl.index;

			conversion_fns.push(expand_conversion_fn(path, variant_name));

			task_variants.push(expand_variant(index, path, variant_name));
		}
	}
	use quote::ToTokens;
	if !task_variants.is_empty() {
		println!(
			"{:#?}",
			task_variants
				.iter()
				.map(|item| item.to_token_stream().to_string())
				.collect::<Vec<_>>()
		);
	}

	quote! {
		/// An aggregation of all `Task` enums across all pallets included in the current runtime.
		#[derive(
			Copy, Clone, Eq, PartialEq, Ord, PartialOrd,
			#scrate::codec::Encode, #scrate::codec::Decode, #scrate::codec::MaxEncodedLen,
			#scrate::scale_info::TypeInfo,
			#scrate::RuntimeDebug,
		)]
		pub enum RuntimeTask {
			#( #task_variants )*
		}

		impl #scrate::traits::AggregatedTask for RuntimeTask {
			fn is_valid(&self) -> bool {
				use #scrate::traits::tasks::prelude::*;
				todo!();
			}

			fn run(&self) -> Result<(), #scrate::traits::tasks::prelude::DispatchError> {
				todo!();
			}

			fn weight(&self) -> Weight {
				todo!();
			}

			fn task_index(&self) -> u64 {
				todo!();
			}
		}

		#( #conversion_fns )*
	}
}

fn expand_conversion_fn(path: &PalletPath, variant_name: &Ident) -> TokenStream {
	quote! {
		impl From<#path::Task> for RuntimeTask {
			fn from(hr: #path::Task) -> Self {
				RuntimeTask::#variant_name(hr)
			}
		}
	}
}

fn expand_variant(index: u8, path: &PalletPath, variant_name: &Ident) -> TokenStream {
	quote! {
		#[codec(index = #index)]
		#variant_name(#path::Task),
	}
}
