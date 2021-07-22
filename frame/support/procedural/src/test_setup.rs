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
use quote::{ToTokens, quote};
use syn::{parse::{Parse, ParseStream}, spanned::Spanned, ItemMacro, Token};

mod keyword {
	syn::custom_keyword!(AccountData);
	syn::custom_keyword!(AccountId);
	syn::custom_keyword!(BaseCallFilter);
	syn::custom_keyword!(BlockHashCount);
	syn::custom_keyword!(BlockLength);
	syn::custom_keyword!(BlockNumber);
	syn::custom_keyword!(BlockWeights);
	syn::custom_keyword!(Call);
	syn::custom_keyword!(DbWeight);
	syn::custom_keyword!(Event);
	syn::custom_keyword!(Hash);
	syn::custom_keyword!(Hashing);
	syn::custom_keyword!(Header);
	syn::custom_keyword!(Index);
	syn::custom_keyword!(Lookup);
	syn::custom_keyword!(OnKilledAccount);
	syn::custom_keyword!(OnNewAccount);
	syn::custom_keyword!(OnSetCode);
	syn::custom_keyword!(Origin);
	syn::custom_keyword!(PalletInfo);
	syn::custom_keyword!(SystemWeightInfo);
	syn::custom_keyword!(SS58Prefix);
	syn::custom_keyword!(Version);
}

#[derive(Debug, Default)]
struct TestSetupAttr {
	account_data: Option<syn::Type>,
	account_id: Option<syn::Type>,
	base_call_filter: Option<syn::Type>,
	block_hash_count: Option<syn::Type>,
	block_length: Option<syn::Type>,
	block_number: Option<syn::Type>,
	block_weights: Option<syn::Type>,
	call: Option<syn::Type>,
	db_weight: Option<syn::Type>,
	event: Option<syn::Type>,
	hash: Option<syn::Type>,
	hashing: Option<syn::Type>,
	header: Option<syn::Type>,
	index: Option<syn::Type>,
	lookup: Option<syn::Type>,
	on_killed_account: Option<syn::Type>,
	on_new_account: Option<syn::Type>,
	on_set_code: Option<syn::Type>,
	origin: Option<syn::Type>,
	pallet_info: Option<syn::Type>,
	system_weight_info: Option<syn::Type>,
	ss58_prefix: Option<syn::Type>,
	version: Option<syn::Type>,
}

impl Parse for TestSetupAttr {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let mut attr = Self::default();
		let mut lookahead = input.lookahead1();

		macro_rules! parse_keyword {
			($attr:ident, $input:ident, $lookahead:ident, $kw:ident, $camel_case:ident) => {
				if $lookahead.peek(keyword::$kw) {
					let _ = $input.parse::<keyword::$kw>();
					$input.parse::<Token![=]>()?;
					$attr.$camel_case = Some($input.parse::<syn::Type>()?);

					if $input.peek(Token![,]) {
						let _ = $input.parse::<Token![,]>();
					}
					$lookahead = $input.lookahead1();
					continue;
				}
			}
		}

		while !input.is_empty() {
			parse_keyword!(attr, input, lookahead, AccountData, account_data);
			parse_keyword!(attr, input, lookahead, AccountId, account_id);
			parse_keyword!(attr, input, lookahead, BaseCallFilter, base_call_filter);
			parse_keyword!(attr, input, lookahead, BlockHashCount, block_hash_count);
			parse_keyword!(attr, input, lookahead, BlockLength, block_length);
			parse_keyword!(attr, input, lookahead, BlockNumber, block_number);
			parse_keyword!(attr, input, lookahead, BlockWeights, block_weights);
			parse_keyword!(attr, input, lookahead, Call, call);
			parse_keyword!(attr, input, lookahead, DbWeight, db_weight);
			parse_keyword!(attr, input, lookahead, Event, event);
			parse_keyword!(attr, input, lookahead, Hash, hash);
			parse_keyword!(attr, input, lookahead, Hashing, hash);
			parse_keyword!(attr, input, lookahead, Header, header);
			parse_keyword!(attr, input, lookahead, Index, index);
			parse_keyword!(attr, input, lookahead, Lookup, lookup);
			parse_keyword!(attr, input, lookahead, OnKilledAccount, on_killed_account);
			parse_keyword!(attr, input, lookahead, OnNewAccount, on_new_account);
			parse_keyword!(attr, input, lookahead, OnSetCode, on_set_code);
			parse_keyword!(attr, input, lookahead, Origin, origin);
			parse_keyword!(attr, input, lookahead, PalletInfo, pallet_info);
			parse_keyword!(attr, input, lookahead, SystemWeightInfo, system_weight_info);
			parse_keyword!(attr, input, lookahead, SS58Prefix, ss58_prefix);
			parse_keyword!(attr, input, lookahead, Version, version);

			// If we reach this point, none of the keywords were successfully parsed
			return Err(lookahead.error());
		}
		Ok(attr)
	}
}

pub fn setup_default_test_parameters(attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
	let ItemMacro { mac, .. } = syn::parse(item)?;
	let attr: TestSetupAttr = if !attr.is_empty() {
		syn::parse(attr)?
	} else {
		Default::default()
	};

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

	let parameter_types = if attr.block_hash_count.is_none() {
		quote! {
			#frame_support::parameter_types! {
				pub const BlockHashCount: u64 = 250;
			}
		}
	} else {
		proc_macro2::TokenStream::new()
	};

	let test_name = runtime_def.name.clone();
	let account_data =
		attr.account_data.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let account_id =
		attr.account_id.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {u64});
	let base_call_filter = attr
		.base_call_filter
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {#frame_support::traits::AllowAll});
	let block_hash_count = attr
		.block_hash_count
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {BlockHashCount});
	let block_length =
		attr.block_length.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let block_number =
		attr.block_number.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {u64});
	let block_weights =
		attr.block_weights.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let call = attr.call.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {Call});
	let db_weight = attr.db_weight.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let event = attr.event.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {Event});
	let hash = attr
		.hash
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {#sp_runtime::testing::H256});
	let hashing = attr
		.hashing
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {#sp_runtime::traits::BlakeTwo256});
	let header = attr
		.header
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {#sp_runtime::testing::Header});
	let index = attr.index.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {u64});
	let lookup = attr
		.lookup
		.as_ref()
		.map(ToTokens::to_token_stream)
		.unwrap_or(quote! {#sp_runtime::traits::IdentityLookup<Self::AccountId>});
	let on_killed_account =
		attr.on_killed_account.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let on_new_account =
		attr.on_new_account.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let on_set_code =
		attr.on_set_code.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let origin = attr.origin.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {Origin});
	let pallet_info =
		attr.pallet_info.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {PalletInfo});
	let system_weight_info =
		attr.system_weight_info.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let ss58_prefix =
		attr.ss58_prefix.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});
	let version = attr.version.as_ref().map(ToTokens::to_token_stream).unwrap_or(quote! {()});

	let runtime = construct_runtime_parsed(runtime_def)?;

	let output = quote! {
		#parameter_types

		impl #frame_system::Config for #test_name {
			type AccountData = #account_data;
			type AccountId = #account_id;
			type BaseCallFilter = #base_call_filter;
			type BlockHashCount = #block_hash_count;
			type BlockLength = #block_length;
			type BlockNumber = #block_number;
			type BlockWeights = #block_weights;
			type Call = #call;
			type DbWeight = #db_weight;
			type Event = #event;
			type Hash = #hash;
			type Hashing = #hashing;
			type Header = #header;
			type Index = #index;
			type Lookup = #lookup;
			type OnKilledAccount = #on_killed_account;
			type OnNewAccount = #on_new_account;
			type OnSetCode = #on_set_code;
			type Origin = #origin;
			type PalletInfo = #pallet_info;
			type SystemWeightInfo = #system_weight_info;
			type SS58Prefix = #ss58_prefix;
			type Version = #version;
		}

		#runtime
	};

	Ok(output.into())
}
