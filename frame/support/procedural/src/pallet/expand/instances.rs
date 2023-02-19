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

use crate::{pallet::Def, NUMBER_OF_INSTANCE};
use proc_macro2::Span;

///
/// * Provide inherent instance to be used by construct_runtime
/// * Provide Instance1 ..= Instance16 for instantiable pallet
pub fn expand_instances(def: &mut Def) -> proc_macro2::TokenStream {
	let frame_support = &def.frame_support;
	let inherent_ident = syn::Ident::new(crate::INHERENT_INSTANCE_NAME, Span::call_site());
	let instances = if def.config.has_instance {
		(1..=NUMBER_OF_INSTANCE)
			.map(|i| syn::Ident::new(&format!("Instance{}", i), Span::call_site()))
			.collect()
	} else {
		vec![]
	};

	quote::quote!(
		/// Hidden instance generated to be internally used when module is used without
		/// instance.
		#[doc(hidden)]
		pub type #inherent_ident = ();

		#( pub use #frame_support::instances::#instances; )*
	)
}
