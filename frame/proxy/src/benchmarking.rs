// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Utility Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::Saturating;
use crate::Module as Proxy;

const SEED: u32 = 0;

fn add_proxies<T: Trait>(n: u32) {
	let caller: T::AccountId = account("caller", 0, SEED);
	for i in 0..n {
		Module::<T>::add_proxy(
			RawOrigin::Signed(caller.clone()).into(),
			account("target", i, SEED),
			T::ProxyType::default()
		);
	}
}

benchmarks! {
	_ {
		let p in 0 .. (T::MaxProxies::get() - 1) => add_proxies(p);
	}

	add_proxy {
		let caller: T::AccountId = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), account("target", 999, SEED), T::ProxyType::default())
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
		});
	}
}
