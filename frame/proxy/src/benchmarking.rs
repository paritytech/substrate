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

// Benchmarks for Proxy Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::Bounded;
use crate::Module as Proxy;

const SEED: u32 = 0;

fn add_proxies<T: Trait>(n: u32, maybe_who: Option<T::AccountId>) -> Result<(), &'static str> {
	let caller = maybe_who.unwrap_or_else(|| account("caller", 0, SEED));
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	for i in 0..n {
		Proxy::<T>::add_proxy(
			RawOrigin::Signed(caller.clone()).into(),
			account("target", i, SEED),
			T::ProxyType::default()
		)?;
	}
	Ok(())
}

benchmarks! {
	_ {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
	}

	proxy {
		let p in ...;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("target", p - 1, SEED);
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = account("caller", 0, SEED);
		let call: <T as Trait>::Call = frame_system::Call::<T>::remark(vec![]).into();
	}: _(RawOrigin::Signed(caller), real, Some(T::ProxyType::default()), Box::new(call))

	add_proxy {
		let p in ...;
		let caller: T::AccountId = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), account("target", T::MaxProxies::get().into(), SEED), T::ProxyType::default())

	remove_proxy {
		let p in ...;
		let caller: T::AccountId = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), account("target", 0, SEED), T::ProxyType::default())

	remove_proxies {
		let p in ...;
		let caller: T::AccountId = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller))

	anonymous {
		let p in ...;
	}: _(RawOrigin::Signed(account("caller", 0, SEED)), T::ProxyType::default(), 0)

	kill_anonymous {
		let p in 0 .. (T::MaxProxies::get() - 2).into();

		let caller: T::AccountId = account("caller", 0, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		Module::<T>::anonymous(RawOrigin::Signed(account("caller", 0, SEED)).into(), T::ProxyType::default(), 0)?;
		let height = system::Module::<T>::block_number();
		let ext_index = system::Module::<T>::extrinsic_index().unwrap_or(0);
		let anon = Module::<T>::anonymous_account(&caller, &T::ProxyType::default(), 0, None);

		add_proxies::<T>(p, Some(anon.clone()))?;

	}: _(RawOrigin::Signed(anon), caller, T::ProxyType::default(), 0, height, ext_index)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_proxy::<Test>());
			assert_ok!(test_benchmark_add_proxy::<Test>());
			assert_ok!(test_benchmark_remove_proxy::<Test>());
			assert_ok!(test_benchmark_remove_proxies::<Test>());
			assert_ok!(test_benchmark_anonymous::<Test>());
			assert_ok!(test_benchmark_kill_anonymous::<Test>());
		});
	}
}
