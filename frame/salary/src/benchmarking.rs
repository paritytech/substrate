// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Staking pallet benchmarking.

use super::*;
#[allow(unused_imports)]
use crate::Pallet as RankedCollective;

use frame_benchmarking::{account, benchmarks_instance_pallet, whitelisted_caller};
use frame_support::{assert_ok, dispatch::UnfilteredDispatchable};
use frame_system::RawOrigin as SystemOrigin;

const SEED: u32 = 0;

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

benchmarks_instance_pallet! {
	add_member {
		let origin = T::PromoteOrigin::successful_origin();
		let call = Call::<T, I>::add_member { };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(MemberCount::<T, I>::get(0), 1);
		assert_last_event::<T, I>(Event::MemberAdded { who }.into());
	}

	impl_benchmark_test_suite!(RankedCollective, crate::tests::new_test_ext(), crate::tests::Test);
}
