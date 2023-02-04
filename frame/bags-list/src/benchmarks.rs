// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the bags list pallet.

use super::*;
use crate::list::List;
use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelist_account, whitelisted_caller,
};
use frame_election_provider_support::ScoreProvider;
use frame_support::{assert_ok, traits::Get};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::One;

benchmarks_instance_pallet! {
	rebag_non_terminal {
		// An expensive case for rebag-ing (rebag a non-terminal node):
		//
		// - The node to be rebagged, _R_, should exist as a non-terminal node in a bag with at
		//   least 2 other nodes. Thus _R_ will have both its `prev` and `next` nodes updated when
		//   it is removed. (3 W/R)
		// - The destination bag is not empty, thus we need to update the `next` pointer of the last
		//   node in the destination in addition to the work we do otherwise. (2 W/R)

		// clear any pre-existing storage.
		// NOTE: safe to call outside block production
		List::<T, _>::unsafe_clear();

		// define our origin and destination thresholds.
		let origin_bag_thresh = T::BagThresholds::get()[0];
		let dest_bag_thresh = T::BagThresholds::get()[1];

		// seed items in the origin bag.
		let origin_head: T::AccountId = account("origin_head", 0, 0);
		assert_ok!(List::<T, _>::insert(origin_head.clone(), origin_bag_thresh));

		let origin_middle: T::AccountId = account("origin_middle", 0, 0); // the node we rebag (_R_)
		assert_ok!(List::<T, _>::insert(origin_middle.clone(), origin_bag_thresh));

		let origin_tail: T::AccountId  = account("origin_tail", 0, 0);
		assert_ok!(List::<T, _>::insert(origin_tail.clone(), origin_bag_thresh));

		// seed items in the destination bag.
		let dest_head: T::AccountId  = account("dest_head", 0, 0);
		assert_ok!(List::<T, _>::insert(dest_head.clone(), dest_bag_thresh));

		let origin_middle_lookup = T::Lookup::unlookup(origin_middle.clone());

		// the bags are in the expected state after initial setup.
		assert_eq!(
			List::<T, _>::get_bags(),
			vec![
				(origin_bag_thresh, vec![origin_head.clone(), origin_middle.clone(), origin_tail.clone()]),
				(dest_bag_thresh, vec![dest_head.clone()])
			]
		);

		let caller = whitelisted_caller();
		// update the weight of `origin_middle` to guarantee it will be rebagged into the destination.
		T::ScoreProvider::set_score_of(&origin_middle, dest_bag_thresh);
	}: rebag(SystemOrigin::Signed(caller), origin_middle_lookup.clone())
	verify {
		// check the bags have updated as expected.
		assert_eq!(
			List::<T, _>::get_bags(),
			vec![
				(
					origin_bag_thresh,
					vec![origin_head, origin_tail],
				),
				(
					dest_bag_thresh,
					vec![dest_head, origin_middle],
				)
			]
		);
	}

	rebag_terminal {
		// An expensive case for rebag-ing (rebag a terminal node):
		//
		// - The node to be rebagged, _R_, is a terminal node; so _R_, the node pointing to _R_ and
		//   the origin bag itself will need to be updated. (3 W/R)
		// - The destination bag is not empty, thus we need to update the `next` pointer of the last
		//   node in the destination in addition to the work we do otherwise. (2 W/R)

		// clear any pre-existing storage.
		// NOTE: safe to call outside block production
		List::<T, I>::unsafe_clear();

		// define our origin and destination thresholds.
		let origin_bag_thresh = T::BagThresholds::get()[0];
		let dest_bag_thresh = T::BagThresholds::get()[1];

		// seed items in the origin bag.
		let origin_head: T::AccountId = account("origin_head", 0, 0);
		assert_ok!(List::<T, _>::insert(origin_head.clone(), origin_bag_thresh));

		let origin_tail: T::AccountId  = account("origin_tail", 0, 0); // the node we rebag (_R_)
		assert_ok!(List::<T, _>::insert(origin_tail.clone(), origin_bag_thresh));

		// seed items in the destination bag.
		let dest_head: T::AccountId  = account("dest_head", 0, 0);
		assert_ok!(List::<T, _>::insert(dest_head.clone(), dest_bag_thresh));

		let origin_tail_lookup = T::Lookup::unlookup(origin_tail.clone());

		// the bags are in the expected state after initial setup.
		assert_eq!(
			List::<T, _>::get_bags(),
			vec![
				(origin_bag_thresh, vec![origin_head.clone(), origin_tail.clone()]),
				(dest_bag_thresh, vec![dest_head.clone()])
			]
		);

		let caller = whitelisted_caller();
		// update the weight of `origin_tail` to guarantee it will be rebagged into the destination.
		T::ScoreProvider::set_score_of(&origin_tail, dest_bag_thresh);
	}: rebag(SystemOrigin::Signed(caller), origin_tail_lookup.clone())
	verify {
		// check the bags have updated as expected.
		assert_eq!(
			List::<T, _>::get_bags(),
			vec![
				(origin_bag_thresh, vec![origin_head.clone()]),
				(dest_bag_thresh, vec![dest_head.clone(), origin_tail])
			]
		);
	}

	put_in_front_of {
		// The most expensive case for `put_in_front_of`:
		//
		// - both heavier's `prev` and `next` are nodes that will need to be read and written.
		// - `lighter` is the bag's `head`, so the bag will need to be read and written.

		// clear any pre-existing storage.
		// NOTE: safe to call outside block production
		List::<T, I>::unsafe_clear();

		let bag_thresh = T::BagThresholds::get()[0];

		// insert the nodes in order
		let lighter: T::AccountId = account("lighter", 0, 0);
		assert_ok!(List::<T, _>::insert(lighter.clone(), bag_thresh));

		let heavier_prev: T::AccountId = account("heavier_prev", 0, 0);
		assert_ok!(List::<T, _>::insert(heavier_prev.clone(), bag_thresh));

		let heavier: T::AccountId = account("heavier", 0, 0);
		assert_ok!(List::<T, _>::insert(heavier.clone(), bag_thresh));

		let heavier_next: T::AccountId = account("heavier_next", 0, 0);
		assert_ok!(List::<T, _>::insert(heavier_next.clone(), bag_thresh));

		T::ScoreProvider::set_score_of(&lighter, bag_thresh - One::one());
		T::ScoreProvider::set_score_of(&heavier, bag_thresh);

		let lighter_lookup = T::Lookup::unlookup(lighter.clone());

		assert_eq!(
			List::<T, _>::iter().map(|n| n.id().clone()).collect::<Vec<_>>(),
			vec![lighter.clone(), heavier_prev.clone(), heavier.clone(), heavier_next.clone()]
		);

		whitelist_account!(heavier);
	}: _(SystemOrigin::Signed(heavier.clone()), lighter_lookup.clone())
	verify {
		assert_eq!(
			List::<T, _>::iter().map(|n| n.id().clone()).collect::<Vec<_>>(),
			vec![heavier, lighter, heavier_prev, heavier_next]
		)
	}

	impl_benchmark_test_suite!(
		Pallet,
		crate::mock::ExtBuilder::default().skip_genesis_ids().build(),
		crate::mock::Runtime
	);
}
