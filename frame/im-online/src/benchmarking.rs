// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! I'm Online pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::benchmarks;
use sp_core::offchain::{OpaquePeerId, OpaqueMultiaddr};
use sp_runtime::traits::{ValidateUnsigned, Zero};
use sp_runtime::transaction_validity::TransactionSource;
use frame_support::traits::UnfilteredDispatchable;

use crate::Module as ImOnline;

const MAX_KEYS: u32 = 1000;
const MAX_EXTERNAL_ADDRESSES: u32 = 100;

pub fn create_heartbeat<T: Trait>(k: u32, e: u32) ->
	Result<(crate::Heartbeat<T::BlockNumber>, <T::AuthorityId as RuntimeAppPublic>::Signature), &'static str>
{
	let mut keys = Vec::new();
	for _ in 0..k {
		keys.push(T::AuthorityId::generate_pair(None));
	}
	Keys::<T>::put(keys.clone());

	let network_state = OpaqueNetworkState {
		peer_id: OpaquePeerId::default(),
		external_addresses: vec![OpaqueMultiaddr::new(vec![0; 32]); e as usize],
	};
	let input_heartbeat = Heartbeat {
		block_number: T::BlockNumber::zero(),
		network_state,
		session_index: 0,
		authority_index: k-1,
		validators_len: keys.len() as u32,
	};

	let encoded_heartbeat = input_heartbeat.encode();
	let authority_id = keys.get((k-1) as usize).ok_or("out of range")?;
	let signature = authority_id.sign(&encoded_heartbeat).ok_or("couldn't make signature")?;

	Ok((input_heartbeat, signature))
}

benchmarks! {
	_{ }

	heartbeat {
		let k in 1 .. MAX_KEYS;
		let e in 1 .. MAX_EXTERNAL_ADDRESSES;
		let (input_heartbeat, signature) = create_heartbeat::<T>(k, e)?;
	}: _(RawOrigin::None, input_heartbeat, signature)

	validate_unsigned {
		let k in 1 .. MAX_KEYS;
		let e in 1 .. MAX_EXTERNAL_ADDRESSES;
		let (input_heartbeat, signature) = create_heartbeat::<T>(k, e)?;
		let call = Call::heartbeat(input_heartbeat, signature);
	}: {
		ImOnline::<T>::validate_unsigned(TransactionSource::InBlock, &call)?;
	}

	validate_unsigned_and_then_heartbeat {
		let k in 1 .. MAX_KEYS;
		let e in 1 .. MAX_EXTERNAL_ADDRESSES;
		let (input_heartbeat, signature) = create_heartbeat::<T>(k, e)?;
		let call = Call::heartbeat(input_heartbeat, signature);
	}: {
		ImOnline::<T>::validate_unsigned(TransactionSource::InBlock, &call)?;
		call.dispatch_bypass_filter(RawOrigin::None.into())?;
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Runtime};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_heartbeat::<Runtime>());
			assert_ok!(test_benchmark_validate_unsigned::<Runtime>());
			assert_ok!(test_benchmark_validate_unsigned_and_then_heartbeat::<Runtime>());
		});
	}
}
