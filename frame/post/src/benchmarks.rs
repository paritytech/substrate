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

// Benchmarks for Post Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::{RawOrigin};
use frame_benchmarking::{benchmarks, whitelisted_caller};
use sp_runtime::traits::Bounded;
use crate::Module as Post;

benchmarks! {
	_ { }

	post {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let post_type = PostType::Blog;
		let topic_vec = vec![0u8; T::MaxTopicLength::get()];
		let post_vec = vec![0u8; T::MaxPostLength::get()];
	}: _(RawOrigin::Signed(caller.clone()), post_type, topic_vec.clone(), post_vec.clone())
	verify {
		assert!(Blog::<T>::get(&caller, &topic_vec).is_some());
	}

	delete {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let post_type = PostType::Blog;
		let topic_vec = vec![0u8; T::MaxTopicLength::get()];
		let post_vec = vec![0u8; T::MaxPostLength::get()];

		Post::<T>::post(
			RawOrigin::Signed(caller.clone()).into(),
			post_type,
			topic_vec.clone(),
			post_vec
		)?;
		assert!(Blog::<T>::get(&caller, &topic_vec).is_some());
	}: _(RawOrigin::Signed(caller.clone()), post_type, topic_vec.clone())
	verify {
		assert!(Blog::<T>::get(&caller, &topic_vec).is_none());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_post::<Test>());
			assert_ok!(test_benchmark_delete::<Test>());
		});
	}
}
