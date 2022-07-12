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
use sp_core::Bytes;
use sp_runtime::{traits::MaybeDisplay, DispatchError};
use sp_std::marker::PhantomData;

pub use pallet_transaction_payment::{FeeDetails, InclusionFee, RuntimeDispatchInfo};

sp_api::decl_runtime_apis! {
	pub trait TransactionPaymentApi<Balance> where
		Balance: Codec + MaybeDisplay,
	{
		fn query_info(uxt: Block::Extrinsic, len: u32) -> RuntimeDispatchInfo<Balance>;
		fn query_fee_details(uxt: Block::Extrinsic, len: u32) -> FeeDetails<Balance>;
		fn query_call_info(encoded_call: Bytes) -> Result<RuntimeDispatchInfo<Balance>, DispatchError>;
		fn query_weight_to_fee(encoded_call: Bytes) -> Result<Balance, DispatchError>;
		// fn query_call_info(call: GetDispatchInfo, len: u32) -> RuntimeDispatchInfo<Balance>;
		// fn query_weight_to_fee(call: GetDispatchInfo) -> Balance;
	}
}

/// Helper type to implement runtime api functions not included to the pallet
pub struct TransactionPayment<T, Balance>(PhantomData<(T, Balance)>);
impl<T, Balance> TransactionPayment<T, Balance>
where
	T: pallet_transaction_payment::Config,
	Balance: Codec + MaybeDisplay,
{
	fn query_call_info(encoded_call: Bytes) -> Result<RuntimeDispatchInfo<Balance>, DispatchError> {
		// let encoded_len = encoded_call.len();
		// let call: Call = Call::decode(&mut &*encoded_call).map_err(|e| {
		// 	Error(e) // TODO map decode error to DispatchError::Module to bubble error info
		// });
		// Ok (RuntimeDispatchInfo {
		// 	weight,
		// 	class,
		// 	partial_fee: pallet_transaction_payment::Pallet::<T>::query_call_info(len, call) })
		unimplemented!();
	}

	fn query_weight_to_fee(encoded_call: Bytes) -> Result<Balance, DispatchError> {
		// let call: Call = Call::decode(&mut &*encoded_call).map_err(|e| {
		// 	Error(e) // TODO map decode error to DispatchError::Module to bubble error info
		// });
		// Ok(pallet_transaction_payment::Pallet::<T>::query_weight_to_fee(call))
		unimplemented!();
	}
}
