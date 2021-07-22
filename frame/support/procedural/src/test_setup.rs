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

use crate::construct_runtime::{construct_runtime_parsed, parse::RuntimeDefinition};
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro::TokenStream;
use quote::quote;
use syn::{spanned::Spanned, ItemMacro};

pub fn setup_default_test_parameters(_attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
	let ItemMacro { mac, .. } = syn::parse(item)?;
	match mac.path.segments.last() {
		Some(segment) if segment.ident == "construct_runtime" => {}
		_ => {
			let msg =
				"Invalid test setup attribute macro: expected `construct_runtime!` macro call";
			let span = mac.path.span();
			return Err(syn::Error::new(span, msg));
		}
	}

	let frame_system = generate_crate_access_2018("frame-system")?;
	let frame_support = generate_crate_access_2018("frame-support")?;
	let sp_runtime = generate_crate_access_2018("sp-runtime")?;
	let runtime_def = mac.parse_body::<RuntimeDefinition>()?;
	let test_name = runtime_def.name.clone();

	let runtime = construct_runtime_parsed(runtime_def)?;

	let output = quote! {
		#frame_support::parameter_types! {
			pub const BlockHashCount: u64 = 250;
		}

		impl #frame_system::Config for #test_name {
			type BaseCallFilter = #frame_support::traits::AllowAll;
			type BlockWeights = ();
			type BlockLength = ();
			type DbWeight = ();
			type Origin = Origin;
			type Index = u64;
			type BlockNumber = u64;
			type Hash = #sp_runtime::testing::H256;
			type Call = Call;
			type Hashing = #sp_runtime::traits::BlakeTwo256;
			type AccountId = u64;
			type Lookup = #sp_runtime::traits::IdentityLookup<Self::AccountId>;
			type Header = #sp_runtime::testing::Header;
			type Event = Event;
			type BlockHashCount = BlockHashCount;
			type Version = ();
			type PalletInfo = PalletInfo;
			type OnNewAccount = ();
			type OnKilledAccount = ();
			type AccountData = ();
			type SystemWeightInfo = ();
			type SS58Prefix = ();
			type OnSetCode = ();
		}

		#runtime
	};

	Ok(output.into())
}
