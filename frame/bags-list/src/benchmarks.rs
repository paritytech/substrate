//! Benchmarks for the bags list pallet.

use super::*;
use crate::list::{Bag, List};
// use frame_benchmarking::{account, whitelisted_caller};
use frame_benchmarking::{account, whitelisted_caller};
use frame_support::traits::Get;
use frame_system::RawOrigin as SystemOrigin;
// use frame_system::RawOrigin;

fn get_bags<T: Config>() -> Vec<(VoteWeight, Vec<T::AccountId>)> {
	T::BagThresholds::get()
		.into_iter()
		.filter_map(|t| {
			Bag::<T>::get(*t)
				.map(|bag| (*t, bag.iter().map(|n| n.id().clone()).collect::<Vec<_>>()))
		})
		.collect::<Vec<_>>()
}

frame_benchmarking::benchmarks! {
	rebag {
		// An expensive case for rebag-ing:
		//
		// - The node to be rebagged should exist as a non-terminal node in a bag with at least
		//   2 other nodes so both its prev and next are nodes that will need be updated
		//   when it is removed.
		// - The destination bag is not empty, because then we need to update the `next` pointer
		//   of the previous node in addition to the work we do otherwise.

		// clear any pre-existing storage.
		List::<T>::clear();

		// define our origin and destination thresholds.
		let origin_bag_thresh = T::BagThresholds::get()[0];
		let dest_bag_thresh = T::BagThresholds::get()[1];

		// seed items in the origin bag.
		let origin_head: T::AccountId = account("origin_head", 0, 0);
		List::<T>::insert(origin_head.clone(), origin_bag_thresh);

		let origin_middle: T::AccountId  = account("origin_middle", 0, 0);
		List::<T>::insert(origin_middle.clone(), origin_bag_thresh);

		let origin_tail: T::AccountId  = account("origin_tail", 0, 0);
		List::<T>::insert(origin_tail.clone(), origin_bag_thresh);

		// seed items in the destination bag.
		let dest_head: T::AccountId  = account("dest_head", 0, 0);
		List::<T>::insert(dest_head.clone(), dest_bag_thresh);

		// and the ags are in the expected state after insertions.
		assert_eq!(
			get_bags::<T>(),
			vec![
				(origin_bag_thresh, vec![origin_head.clone(), origin_middle.clone(), origin_tail.clone()]),
				(dest_bag_thresh, vec![dest_head.clone()])
			]
		);

		let caller = whitelisted_caller();
		T::VoteWeightProvider::set_vote_weight_of(&origin_middle, dest_bag_thresh);
	}: _(SystemOrigin::Signed(caller), origin_middle.clone())
	verify {
		// check the bags have updated as expected.
		assert_eq!(
			get_bags::<T>(),
			vec![(origin_bag_thresh, vec![origin_head, origin_tail]), (dest_bag_thresh, vec![dest_head, origin_middle])]
		);
	}
}

use frame_benchmarking::impl_benchmark_test_suite;
impl_benchmark_test_suite!(
	Pallet,
	crate::mock::ext_builder::ExtBuilder::default().build(),
	crate::mock::Runtime,
);
