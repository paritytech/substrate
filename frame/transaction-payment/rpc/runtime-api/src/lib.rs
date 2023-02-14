// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for transaction payment pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use sp_runtime::traits::MaybeDisplay;

pub use pallet_transaction_payment::{FeeDetails, InclusionFee, RuntimeDispatchInfo};

sp_api::decl_runtime_apis! {
	#[api_version(3)]
	pub trait TransactionPaymentApi<Balance> where
		Balance: Codec + MaybeDisplay,
	{
		#[changed_in(2)]
		fn query_info(uxt: Block::Extrinsic, len: u32) -> RuntimeDispatchInfo<Balance, sp_weights::OldWeight>;
		fn query_info(uxt: Block::Extrinsic, len: u32) -> RuntimeDispatchInfo<Balance>;
		fn query_fee_details(uxt: Block::Extrinsic, len: u32) -> FeeDetails<Balance>;
		fn query_weight_to_fee(weight: sp_weights::Weight) -> Balance;
		fn query_length_to_fee(length: u32) -> Balance;
	}

	#[api_version(3)]
	pub trait TransactionPaymentCallApi<Balance, Call>
	where
		Balance: Codec + MaybeDisplay,
		Call: Codec,
	{
		/// Query information of a dispatch class, weight, and fee of a given encoded `Call`.
		fn query_call_info(call: Call, len: u32) -> RuntimeDispatchInfo<Balance>;

		/// Query fee details of a given encoded `Call`.
		fn query_call_fee_details(call: Call, len: u32) -> FeeDetails<Balance>;

		/// Query the output of the current `WeightToFee` given some input.
		fn query_weight_to_fee(weight: sp_weights::Weight) -> Balance;

		/// Query the output of the current `LengthToFee` given some input.
		fn query_length_to_fee(length: u32) -> Balance;
	}
}
