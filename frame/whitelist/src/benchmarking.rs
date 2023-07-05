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

//! Whitelist pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::v1::{benchmarks, BenchmarkError};
use frame_support::{ensure, traits::EnsureOrigin};

#[cfg(test)]
use crate::Pallet as Whitelist;

benchmarks! {
	whitelist_call {
		let origin =
			T::WhitelistOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call_hash = Default::default();
	}: _<T::RuntimeOrigin>(origin, call_hash)
	verify {
		ensure!(
			WhitelistedCall::<T>::contains_key(call_hash),
			"call not whitelisted"
		);
		ensure!(
			T::Preimages::is_requested(&call_hash),
			"preimage not requested"
		);
	}

	remove_whitelisted_call {
		let origin =
			T::WhitelistOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call_hash = Default::default();
		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");
	}: _<T::RuntimeOrigin>(origin, call_hash)
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::Preimages::is_requested(&call_hash),
			"preimage still requested"
		);
	}

	// We benchmark with the maximum possible size for a call.
	// If the resulting weight is too big, maybe it worth having a weight which depends
	// on the size of the call, with a new witness in parameter.
	#[pov_mode = MaxEncodedLen {
		// Use measured PoV size for the Preimages since we pass in a length witness.
		Preimage::PreimageFor: Measured
	}]
	dispatch_whitelisted_call {
		// NOTE: we remove `10` because we need some bytes to encode the variants and vec length
		let n in 1 .. T::Preimages::MAX_LENGTH as u32 - 10;

		let origin = T::DispatchWhitelistedOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;
		let remark = sp_std::vec![1u8; n as usize];
		let call: <T as Config>::RuntimeCall = frame_system::Call::remark { remark }.into();
		let call_weight = call.get_dispatch_info().weight;
		let encoded_call = call.encode();
		let call_encoded_len = encoded_call.len() as u32;
		let call_hash = call.blake2_256().into();

		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");

		T::Preimages::note(encoded_call.into()).unwrap();

	}: _<T::RuntimeOrigin>(origin, call_hash, call_encoded_len, call_weight)
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::Preimages::is_requested(&call_hash),
			"preimage still requested"
		);
	}

	dispatch_whitelisted_call_with_preimage {
		let n in 1 .. 10_000;

		let origin = T::DispatchWhitelistedOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;
		let remark = sp_std::vec![1u8; n as usize];

		let call: <T as Config>::RuntimeCall = frame_system::Call::remark { remark }.into();
		let call_hash = call.blake2_256().into();

		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");
	}: _<T::RuntimeOrigin>(origin, Box::new(call))
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::Preimages::is_requested(&call_hash),
			"preimage still requested"
		);
	}

	impl_benchmark_test_suite!(Whitelist, crate::mock::new_test_ext(), crate::mock::Test);
}
