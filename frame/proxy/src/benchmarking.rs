// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
use frame_system::{RawOrigin, EventRecord};
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use sp_runtime::traits::Bounded;
use crate::Module as Proxy;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

fn add_proxies<T: Config>(n: u32, maybe_who: Option<T::AccountId>) -> Result<(), &'static str> {
	let caller = maybe_who.unwrap_or_else(|| whitelisted_caller());
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	for i in 0..n {
		Proxy::<T>::add_proxy(
			RawOrigin::Signed(caller.clone()).into(),
			account("target", i, SEED),
			T::ProxyType::default(),
			T::BlockNumber::zero(),
		)?;
	}
	Ok(())
}

fn add_announcements<T: Config>(
	n: u32,
	maybe_who: Option<T::AccountId>,
	maybe_real: Option<T::AccountId>
) -> Result<(), &'static str> {
	let caller = maybe_who.unwrap_or_else(|| account("caller", 0, SEED));
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	let real = if let Some(real) = maybe_real {
		real
	} else {
		let real = account("real", 0, SEED);
		T::Currency::make_free_balance_be(&real, BalanceOf::<T>::max_value());
		Proxy::<T>::add_proxy(
			RawOrigin::Signed(real.clone()).into(),
			caller.clone(),
			T::ProxyType::default(),
			T::BlockNumber::zero(),
		)?;
		real
	};
	for _ in 0..n {
		Proxy::<T>::announce(
			RawOrigin::Signed(caller.clone()).into(),
			real.clone(),
			T::CallHasher::hash_of(&("add_announcement", n)),
		)?;
	}
	Ok(())
}

benchmarks! {
	proxy {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("target", p - 1, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = whitelisted_caller();
		let call: <T as Config>::Call = frame_system::Call::<T>::remark(vec![]).into();
	}: _(RawOrigin::Signed(caller), real, Some(T::ProxyType::default()), Box::new(call))
	verify {
		assert_last_event::<T>(RawEvent::ProxyExecuted(Ok(())).into())
	}

	proxy_announced {
		let a in 0 .. T::MaxPending::get() - 1;
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("anonymous", 0, SEED);
		let delegate: T::AccountId = account("target", p - 1, SEED);
		T::Currency::make_free_balance_be(&delegate, BalanceOf::<T>::max_value());
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = whitelisted_caller();
		let call: <T as Config>::Call = frame_system::Call::<T>::remark(vec![]).into();
		Proxy::<T>::announce(
			RawOrigin::Signed(delegate.clone()).into(),
			real.clone(),
			T::CallHasher::hash_of(&call),
		)?;
		add_announcements::<T>(a, Some(delegate.clone()), None)?;
	}: _(RawOrigin::Signed(caller), delegate, real, Some(T::ProxyType::default()), Box::new(call))
	verify {
		assert_last_event::<T>(RawEvent::ProxyExecuted(Ok(())).into())
	}

	remove_announcement {
		let a in 0 .. T::MaxPending::get() - 1;
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("target", p - 1, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = whitelisted_caller();
		let call: <T as Config>::Call = frame_system::Call::<T>::remark(vec![]).into();
		Proxy::<T>::announce(
			RawOrigin::Signed(caller.clone()).into(),
			real.clone(),
			T::CallHasher::hash_of(&call),
		)?;
		add_announcements::<T>(a, Some(caller.clone()), None)?;
	}: _(RawOrigin::Signed(caller.clone()), real, T::CallHasher::hash_of(&call))
	verify {
		let (announcements, _) = Announcements::<T>::get(&caller);
		assert_eq!(announcements.len() as u32, a);
	}

	reject_announcement {
		let a in 0 .. T::MaxPending::get() - 1;
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("target", p - 1, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = whitelisted_caller();
		let call: <T as Config>::Call = frame_system::Call::<T>::remark(vec![]).into();
		Proxy::<T>::announce(
			RawOrigin::Signed(caller.clone()).into(),
			real.clone(),
			T::CallHasher::hash_of(&call),
		)?;
		add_announcements::<T>(a, Some(caller.clone()), None)?;
	}: _(RawOrigin::Signed(real), caller.clone(), T::CallHasher::hash_of(&call))
	verify {
		let (announcements, _) = Announcements::<T>::get(&caller);
		assert_eq!(announcements.len() as u32, a);
	}

	announce {
		let a in 0 .. T::MaxPending::get() - 1;
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		// In this case the caller is the "target" proxy
		let caller: T::AccountId = account("target", p - 1, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		// ... and "real" is the traditional caller. This is not a typo.
		let real: T::AccountId = whitelisted_caller();
		add_announcements::<T>(a, Some(caller.clone()), None)?;
		let call: <T as Config>::Call = frame_system::Call::<T>::remark(vec![]).into();
		let call_hash = T::CallHasher::hash_of(&call);
	}: _(RawOrigin::Signed(caller.clone()), real.clone(), call_hash)
	verify {
		assert_last_event::<T>(RawEvent::Announced(real, caller, call_hash).into());
	}

	add_proxy {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		let caller: T::AccountId = whitelisted_caller();
	}: _(
		RawOrigin::Signed(caller.clone()),
		account("target", T::MaxProxies::get().into(), SEED),
		T::ProxyType::default(),
		T::BlockNumber::zero()
	)
	verify {
		let (proxies, _) = Proxies::<T>::get(caller);
		assert_eq!(proxies.len() as u32, p + 1);
	}

	remove_proxy {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		let caller: T::AccountId = whitelisted_caller();
	}: _(
		RawOrigin::Signed(caller.clone()),
		account("target", 0, SEED),
		T::ProxyType::default(),
		T::BlockNumber::zero()
	)
	verify {
		let (proxies, _) = Proxies::<T>::get(caller);
		assert_eq!(proxies.len() as u32, p - 1);
	}

	remove_proxies {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		let caller: T::AccountId = whitelisted_caller();
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		let (proxies, _) = Proxies::<T>::get(caller);
		assert_eq!(proxies.len() as u32, 0);
	}

	anonymous {
		let p in 1 .. (T::MaxProxies::get() - 1).into() => add_proxies::<T>(p, None)?;
		let caller: T::AccountId = whitelisted_caller();
	}: _(
		RawOrigin::Signed(caller.clone()),
		T::ProxyType::default(),
		T::BlockNumber::zero(),
		0
	)
	verify {
		let anon_account = Module::<T>::anonymous_account(&caller, &T::ProxyType::default(), 0, None);
		assert_last_event::<T>(RawEvent::AnonymousCreated(
			anon_account,
			caller,
			T::ProxyType::default(),
			0,
		).into());
	}

	kill_anonymous {
		let p in 0 .. (T::MaxProxies::get() - 2).into();

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		Module::<T>::anonymous(
			RawOrigin::Signed(whitelisted_caller()).into(),
			T::ProxyType::default(),
			T::BlockNumber::zero(),
			0
		)?;
		let height = system::Module::<T>::block_number();
		let ext_index = system::Module::<T>::extrinsic_index().unwrap_or(0);
		let anon = Module::<T>::anonymous_account(&caller, &T::ProxyType::default(), 0, None);

		add_proxies::<T>(p, Some(anon.clone()))?;
		ensure!(Proxies::<T>::contains_key(&anon), "anon proxy not created");
	}: _(RawOrigin::Signed(anon.clone()), caller.clone(), T::ProxyType::default(), 0, height, ext_index)
	verify {
		assert!(!Proxies::<T>::contains_key(&anon));
	}
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
			assert_ok!(test_benchmark_proxy_announced::<Test>());
			assert_ok!(test_benchmark_remove_announcement::<Test>());
			assert_ok!(test_benchmark_reject_announcement::<Test>());
			assert_ok!(test_benchmark_announce::<Test>());
			assert_ok!(test_benchmark_add_proxy::<Test>());
			assert_ok!(test_benchmark_remove_proxy::<Test>());
			assert_ok!(test_benchmark_remove_proxies::<Test>());
			assert_ok!(test_benchmark_anonymous::<Test>());
			assert_ok!(test_benchmark_kill_anonymous::<Test>());
		});
	}
}
