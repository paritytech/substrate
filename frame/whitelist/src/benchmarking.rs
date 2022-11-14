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

//! Whitelist pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::benchmarks;
use frame_support::{
	ensure,
	traits::{EnsureOrigin, Get, PreimageRecipient},
};

#[cfg(test)]
use crate::Pallet as Whitelist;

benchmarks! {
	whitelist_call {
		let origin = T::WhitelistOrigin::successful_origin();
		let call_hash = Default::default();
	}: _<T::Origin>(origin, call_hash)
	verify {
		ensure!(
			WhitelistedCall::<T>::contains_key(call_hash),
			"call not whitelisted"
		);
		ensure!(
			T::PreimageProvider::preimage_requested(&call_hash),
			"preimage not requested"
		);
	}

	remove_whitelisted_call {
		let origin = T::WhitelistOrigin::successful_origin();
		let call_hash = Default::default();
		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");
	}: _<T::Origin>(origin, call_hash)
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::PreimageProvider::preimage_requested(&call_hash),
			"preimage still requested"
		);
	}

	// We benchmark with the maximum possible size for a call.
	// If the resulting weight is too big, maybe it worth having a weight which depends
	// on the size of the call, with a new witness in parameter.
	dispatch_whitelisted_call {
		let origin = T::DispatchWhitelistedOrigin::successful_origin();
		// NOTE: we remove `10` because we need some bytes to encode the variants and vec length
		let remark_len = <T::PreimageProvider as PreimageRecipient<_>>::MaxSize::get() - 10;
		let remark = sp_std::vec![1u8; remark_len as usize];

		let call: <T as Config>::Call = frame_system::Call::remark { remark }.into();
		let call_weight = call.get_dispatch_info().weight;
		let encoded_call = call.encode();
		let call_hash = T::Hashing::hash(&encoded_call[..]);

		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");

		let encoded_call = encoded_call.try_into().expect("encoded_call must be small enough");
		T::PreimageProvider::note_preimage(encoded_call);

	}: _<T::Origin>(origin, call_hash, call_weight)
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::PreimageProvider::preimage_requested(&call_hash),
			"preimage still requested"
		);
	}

	dispatch_whitelisted_call_with_preimage {
		let n in 1 .. 10_000;

		let origin = T::DispatchWhitelistedOrigin::successful_origin();
		let remark = sp_std::vec![1u8; n as usize];

		let call: <T as Config>::Call = frame_system::Call::remark { remark }.into();
		let call_hash = T::Hashing::hash_of(&call);

		Pallet::<T>::whitelist_call(origin.clone(), call_hash)
			.expect("whitelisting call must be successful");
	}: _<T::Origin>(origin, Box::new(call))
	verify {
		ensure!(
			!WhitelistedCall::<T>::contains_key(call_hash),
			"whitelist not removed"
		);
		ensure!(
			!T::PreimageProvider::preimage_requested(&call_hash),
			"preimage still requested"
		);
	}

	impl_benchmark_test_suite!(Whitelist, crate::mock::new_test_ext(), crate::mock::Test);
}
