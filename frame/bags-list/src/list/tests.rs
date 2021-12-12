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

use super::*;
use crate::{
	mock::{test_utils::*, *},
	ListBags, ListNodes,
};
use frame_election_provider_support::SortedListProvider;
use frame_support::{assert_ok, assert_storage_noop};

#[test]
fn basic_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		// syntactic sugar to create a raw node
		let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };

		assert_eq!(ListNodes::<Runtime>::count(), 4);
		assert_eq!(ListNodes::<Runtime>::iter().count(), 4);
		assert_eq!(ListBags::<Runtime>::iter().count(), 2);

		assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

		// the state of the bags is as expected
		assert_eq!(
			ListBags::<Runtime>::get(10).unwrap(),
			Bag::<Runtime> { head: Some(1), tail: Some(1), bag_upper: 0 }
		);
		assert_eq!(
			ListBags::<Runtime>::get(1_000).unwrap(),
			Bag::<Runtime> { head: Some(2), tail: Some(4), bag_upper: 0 }
		);

		assert_eq!(ListNodes::<Runtime>::get(2).unwrap(), node(2, None, Some(3), 1_000));
		assert_eq!(ListNodes::<Runtime>::get(3).unwrap(), node(3, Some(2), Some(4), 1_000));
		assert_eq!(ListNodes::<Runtime>::get(4).unwrap(), node(4, Some(3), None, 1_000));
		assert_eq!(ListNodes::<Runtime>::get(1).unwrap(), node(1, None, None, 10));

		// non-existent id does not have a storage footprint
		assert_eq!(ListNodes::<Runtime>::get(42), None);

		// iteration of the bags would yield:
		assert_eq!(
			List::<Runtime>::iter().map(|n| *n.id()).collect::<Vec<_>>(),
			vec![2, 3, 4, 1],
			//   ^^ note the order of insertion in genesis!
		);
	});
}

#[test]
fn notional_bag_for_works() {
	// under a threshold gives the next threshold.
	assert_eq!(notional_bag_for::<Runtime>(0), 10);
	assert_eq!(notional_bag_for::<Runtime>(9), 10);

	// at a threshold gives that threshold.
	assert_eq!(notional_bag_for::<Runtime>(10), 10);

	// above the threshold, gives the next threshold.
	assert_eq!(notional_bag_for::<Runtime>(11), 20);

	let max_explicit_threshold = *<Runtime as Config>::BagThresholds::get().last().unwrap();
	assert_eq!(max_explicit_threshold, 10_000);

	// if the max explicit threshold is less than VoteWeight::MAX,
	assert!(VoteWeight::MAX > max_explicit_threshold);

	// then anything above it will belong to the VoteWeight::MAX bag.
	assert_eq!(notional_bag_for::<Runtime>(max_explicit_threshold), max_explicit_threshold);
	assert_eq!(notional_bag_for::<Runtime>(max_explicit_threshold + 1), VoteWeight::MAX);
}

#[test]
fn remove_last_node_in_bags_cleans_bag() {
	ExtBuilder::default().build_and_execute(|| {
		// given
		assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

		// bump 1 to a bigger bag
		List::<Runtime>::remove(&1);
		assert_ok!(List::<Runtime>::insert(1, 10_000));

		// then the bag with bound 10 is wiped from storage.
		assert_eq!(List::<Runtime>::get_bags(), vec![(1_000, vec![2, 3, 4]), (10_000, vec![1])]);

		// and can be recreated again as needed.
		assert_ok!(List::<Runtime>::insert(77, 10));
		assert_eq!(
			List::<Runtime>::get_bags(),
			vec![(10, vec![77]), (1_000, vec![2, 3, 4]), (10_000, vec![1])]
		);
	});
}

#[test]
fn migrate_works() {
	ExtBuilder::default()
		.add_ids(vec![(710, 15), (711, 16), (712, 2_000)])
		.build_and_execute(|| {
			// given
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![
					(10, vec![1]),
					(20, vec![710, 711]),
					(1_000, vec![2, 3, 4]),
					(2_000, vec![712])
				]
			);
			let old_thresholds = <Runtime as Config>::BagThresholds::get();
			assert_eq!(old_thresholds, vec![10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000]);

			// when the new thresholds adds `15` and removes `2_000`
			const NEW_THRESHOLDS: &'static [VoteWeight] =
				&[10, 15, 20, 30, 40, 50, 60, 1_000, 10_000];
			BagThresholds::set(NEW_THRESHOLDS);
			// and we call
			List::<Runtime>::migrate(old_thresholds);

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![
					(10, vec![1]),
					(15, vec![710]), // nodes in range 11 ..= 15 move from bag 20 to bag 15
					(20, vec![711]),
					(1_000, vec![2, 3, 4]),
					// nodes in range 1_001 ..= 2_000 move from bag 2_000 to bag 10_000
					(10_000, vec![712]),
				]
			);
		});
}

mod list {
	use super::*;

	#[test]
	fn iteration_is_semi_sorted() {
		ExtBuilder::default()
			.add_ids(vec![(5, 2_000), (6, 2_000)])
			.build_and_execute(|| {
				// given
				assert_eq!(
					List::<Runtime>::get_bags(),
					vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2_000, vec![5, 6])]
				);
				assert_eq!(
					get_list_as_ids(),
					vec![
						5, 6, // best bag
						2, 3, 4, // middle bag
						1, // last bag.
					]
				);

				// when adding an id that has a higher weight than pre-existing ids in the bag
				assert_ok!(List::<Runtime>::insert(7, 10));

				// then
				assert_eq!(
					get_list_as_ids(),
					vec![
						5, 6, // best bag
						2, 3, 4, // middle bag
						1, 7, // last bag; new id is last.
					]
				);
			})
	}

	/// we can `take` x ids, even if that quantity ends midway through a list.
	#[test]
	fn take_works() {
		ExtBuilder::default()
			.add_ids(vec![(5, 2_000), (6, 2_000)])
			.build_and_execute(|| {
				// given
				assert_eq!(
					List::<Runtime>::get_bags(),
					vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2_000, vec![5, 6])]
				);

				// when
				let iteration =
					List::<Runtime>::iter().map(|node| *node.id()).take(4).collect::<Vec<_>>();

				// then
				assert_eq!(
					iteration,
					vec![
						5, 6, // best bag, fully iterated
						2, 3, // middle bag, partially iterated
					]
				);
			})
	}

	#[test]
	fn insert_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when inserting into an existing bag
			assert_ok!(List::<Runtime>::insert(5, 1_000));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5])]);
			assert_eq!(get_list_as_ids(), vec![2, 3, 4, 5, 1]);

			// when inserting into a non-existent bag
			assert_ok!(List::<Runtime>::insert(6, 1_001));

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5]), (2_000, vec![6])]
			);
			assert_eq!(get_list_as_ids(), vec![6, 2, 3, 4, 5, 1]);
		});
	}

	#[test]
	fn insert_errors_with_duplicate_id() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert!(get_list_as_ids().contains(&3));

			// then
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::insert(3, 20).unwrap_err(),
				Error::Duplicate
			));
		});
	}

	#[test]
	fn remove_works() {
		use crate::{ListBags, ListNodes};
		let ensure_left = |id, counter| {
			assert!(!ListNodes::<Runtime>::contains_key(id));
			assert_eq!(ListNodes::<Runtime>::count(), counter);
			assert_eq!(ListNodes::<Runtime>::iter().count() as u32, counter);
		};

		ExtBuilder::default().build_and_execute(|| {
			// removing a non-existent id is a noop
			assert!(!ListNodes::<Runtime>::contains_key(42));
			assert_storage_noop!(List::<Runtime>::remove(&42));

			// when removing a node from a bag with multiple nodes:
			List::<Runtime>::remove(&2);

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4, 1]);
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 4])]);
			ensure_left(2, 3);

			// when removing a node from a bag with only one node:
			List::<Runtime>::remove(&1);

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4]);
			assert_eq!(List::<Runtime>::get_bags(), vec![(1_000, vec![3, 4])]);
			ensure_left(1, 2);
			// bag 10 is removed
			assert!(!ListBags::<Runtime>::contains_key(10));

			// remove remaining ids to make sure storage cleans up as expected
			List::<Runtime>::remove(&3);
			ensure_left(3, 1);
			assert_eq!(get_list_as_ids(), vec![4]);

			List::<Runtime>::remove(&4);
			ensure_left(4, 0);
			assert_eq!(get_list_as_ids(), Vec::<AccountId>::new());

			// bags are deleted via removals
			assert_eq!(ListBags::<Runtime>::iter().count(), 0);
		});
	}

	#[test]
	fn remove_many_is_noop_with_non_existent_ids() {
		ExtBuilder::default().build_and_execute(|| {
			let non_existent_ids = vec![&42, &666, &13];

			// when account ids don' exist in the list
			assert!(non_existent_ids.iter().all(|id| !BagsList::contains(id)));

			// then removing them is a noop
			assert_storage_noop!(List::<Runtime>::remove_many(non_existent_ids));
		});
	}

	#[test]
	fn update_position_for_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given a correctly placed account 1 at bag 10.
			let node = Node::<Runtime>::get(&1).unwrap();
			assert!(!node.is_misplaced(10));

			// .. it is invalid with weight 20
			assert!(node.is_misplaced(20));

			// move it to bag 20.
			assert_eq!(List::<Runtime>::update_position_for(node, 20), Some((10, 20)));

			assert_eq!(List::<Runtime>::get_bags(), vec![(20, vec![1]), (1_000, vec![2, 3, 4])]);

			// get the new updated node; try and update the position with no change in weight.
			let node = Node::<Runtime>::get(&1).unwrap();
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node.clone(), 20),
				None
			));

			// then move it to bag 1_000 by giving it weight 500.
			assert_eq!(List::<Runtime>::update_position_for(node.clone(), 500), Some((20, 1_000)));
			assert_eq!(List::<Runtime>::get_bags(), vec![(1_000, vec![2, 3, 4, 1])]);

			// moving within that bag again is a noop
			let node = Node::<Runtime>::get(&1).unwrap();
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node.clone(), 750),
				None,
			));
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node, 1_000),
				None,
			));
		});
	}

	#[test]
	fn sanity_check_works() {
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			assert_ok!(List::<Runtime>::sanity_check());
		});

		// make sure there are no duplicates.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			Bag::<Runtime>::get(10).unwrap().insert_unchecked(2);
			assert_eq!(List::<Runtime>::sanity_check(), Err("duplicate identified"));
		});

		// ensure count is in sync with `ListNodes::count()`.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			assert_eq!(crate::ListNodes::<Runtime>::count(), 4);
			// we do some wacky stuff here to get access to the counter, since it is (reasonably)
			// not exposed as mutable in any sense.
			frame_support::generate_storage_alias!(
				BagsList,
				CounterForListNodes
				=> Value<u32, frame_support::pallet_prelude::ValueQuery>
			);
			CounterForListNodes::mutate(|counter| *counter += 1);
			assert_eq!(crate::ListNodes::<Runtime>::count(), 5);

			assert_eq!(List::<Runtime>::sanity_check(), Err("iter_count != stored_count"));
		});
	}

	#[test]
	fn contains_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert!(GENESIS_IDS.iter().all(|(id, _)| List::<Runtime>::contains(id)));

			let non_existent_ids = vec![&42, &666, &13];
			assert!(non_existent_ids.iter().all(|id| !List::<Runtime>::contains(id)));
		})
	}

	#[test]
	#[should_panic = "given nodes must always have a valid bag. qed."]
	fn put_in_front_of_panics_if_bag_not_found() {
		ExtBuilder::default().skip_genesis_ids().build_and_execute_no_post_check(|| {
			let node_10_no_bag = Node::<Runtime> { id: 10, prev: None, next: None, bag_upper: 15 };
			let node_11_no_bag = Node::<Runtime> { id: 11, prev: None, next: None, bag_upper: 15 };

			// given
			ListNodes::<Runtime>::insert(10, node_10_no_bag);
			ListNodes::<Runtime>::insert(11, node_11_no_bag);
			StakingMock::set_vote_weight_of(&10, 14);
			StakingMock::set_vote_weight_of(&11, 15);
			assert!(!ListBags::<Runtime>::contains_key(15));
			assert_eq!(List::<Runtime>::get_bags(), vec![]);

			// then .. this panics
			let _ = List::<Runtime>::put_in_front_of(&10, &11);
		});
	}

	#[test]
	fn insert_at_unchecked_at_is_only_node() {
		// Note that this `insert_at_unchecked` test should fail post checks because node 42 does
		// not get re-assigned the correct bagu pper. This is because `insert_at_unchecked` assumes
		// both nodes are already in the same bag with the correct bag upper.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// implicitly also test that `node`'s `prev`/`next` are correctly re-assigned.
			let node_42 =
				Node::<Runtime> { id: 42, prev: Some(1), next: Some(2), bag_upper: 1_000 };
			assert!(!crate::ListNodes::<Runtime>::contains_key(42));

			let node_1 = crate::ListNodes::<Runtime>::get(&1).unwrap();

			// when
			List::<Runtime>::insert_at_unchecked(node_1, node_42);

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![42, 1]), (1_000, vec![2, 3, 4])]
			);
		})
	}

	#[test]
	fn insert_at_unchecked_at_is_head() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// implicitly also test that `node`'s `prev`/`next` are correctly re-assigned.
			let node_42 = Node::<Runtime> { id: 42, prev: Some(4), next: None, bag_upper: 1_000 };
			assert!(!crate::ListNodes::<Runtime>::contains_key(42));

			let node_2 = crate::ListNodes::<Runtime>::get(&2).unwrap();

			// when
			List::<Runtime>::insert_at_unchecked(node_2, node_42);

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![42, 2, 3, 4])]
			);
		})
	}

	#[test]
	fn insert_at_unchecked_at_is_non_terminal() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// implicitly also test that `node`'s `prev`/`next` are correctly re-assigned.
			let node_42 = Node::<Runtime> { id: 42, prev: None, next: Some(2), bag_upper: 1_000 };
			assert!(!crate::ListNodes::<Runtime>::contains_key(42));

			let node_3 = crate::ListNodes::<Runtime>::get(&3).unwrap();

			// when
			List::<Runtime>::insert_at_unchecked(node_3, node_42);

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 42, 3, 4])]
			);
		})
	}

	#[test]
	fn insert_at_unchecked_at_is_tail() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// implicitly also test that `node`'s `prev`/`next` are correctly re-assigned.
			let node_42 =
				Node::<Runtime> { id: 42, prev: Some(42), next: Some(42), bag_upper: 1_000 };
			assert!(!crate::ListNodes::<Runtime>::contains_key(42));

			let node_4 = crate::ListNodes::<Runtime>::get(&4).unwrap();

			// when
			List::<Runtime>::insert_at_unchecked(node_4, node_42);

			// then
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 42, 4])]
			);
		})
	}
}

mod bags {
	use super::*;

	#[test]
	fn get_works() {
		ExtBuilder::default().build_and_execute(|| {
			let check_bag = |bag_upper, head, tail, ids| {
				let bag = Bag::<Runtime>::get(bag_upper).unwrap();
				let bag_ids = bag.iter().map(|n| *n.id()).collect::<Vec<_>>();

				assert_eq!(bag, Bag::<Runtime> { head, tail, bag_upper });
				assert_eq!(bag_ids, ids);
			};

			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// we can fetch them
			check_bag(10, Some(1), Some(1), vec![1]);
			check_bag(1_000, Some(2), Some(4), vec![2, 3, 4]);

			// and all other bag thresholds don't get bags.
			<Runtime as Config>::BagThresholds::get()
				.iter()
				.chain(iter::once(&VoteWeight::MAX))
				.filter(|bag_upper| !vec![10, 1_000].contains(bag_upper))
				.for_each(|bag_upper| {
					assert_storage_noop!(assert_eq!(Bag::<Runtime>::get(*bag_upper), None));
					assert!(!ListBags::<Runtime>::contains_key(*bag_upper));
				});

			// when we make a pre-existing bag empty
			List::<Runtime>::remove(&1);

			// then
			assert_eq!(Bag::<Runtime>::get(10), None)
		});
	}

	#[test]
	fn insert_node_sets_proper_bag() {
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			let node = |id, bag_upper| Node::<Runtime> { id, prev: None, next: None, bag_upper };

			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			bag_10.insert_node_unchecked(node(42, 5));

			assert_eq!(
				ListNodes::<Runtime>::get(&42).unwrap(),
				Node { bag_upper: 10, prev: Some(1), next: None, id: 42 }
			);
		});
	}

	#[test]
	fn insert_node_happy_paths_works() {
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			let node = |id, bag_upper| Node::<Runtime> { id, prev: None, next: None, bag_upper };

			// when inserting into a bag with 1 node
			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			bag_10.insert_node_unchecked(node(42, bag_10.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_10), vec![1, 42]);

			// when inserting into a bag with 3 nodes
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node_unchecked(node(52, bag_1000.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4, 52]);

			// when inserting into a new bag
			let mut bag_20 = Bag::<Runtime>::get_or_make(20);
			bag_20.insert_node_unchecked(node(62, bag_20.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_20), vec![62]);

			// when inserting a node pointing to the accounts not in the bag
			let node_61 =
				Node::<Runtime> { id: 61, prev: Some(21), next: Some(101), bag_upper: 20 };
			bag_20.insert_node_unchecked(node_61);
			// then ids are in order
			assert_eq!(bag_as_ids(&bag_20), vec![62, 61]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(&61).unwrap(),
				Node::<Runtime> { id: 61, prev: Some(62), next: None, bag_upper: 20 }
			);

			// state of all bags is as expected
			bag_20.put(); // need to put this newly created bag so its in the storage map
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1, 42]), (20, vec![62, 61]), (1_000, vec![2, 3, 4, 52])]
			);
		});
	}

	// Document improper ways `insert_node` may be getting used.
	#[test]
	fn insert_node_bad_paths_documented() {
		let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// when inserting a node with both prev & next pointing at an account in an incorrect
			// bag.
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node_unchecked(node(42, Some(1), Some(1), 500));

			// then the proper prev and next is set.
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4, 42]);

			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(&42).unwrap(),
				node(42, Some(4), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// given 3 is in bag_1000 (and not a tail node)
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4]);

			// when inserting a node with duplicate id 3
			bag_1000.insert_node_unchecked(node(3, None, None, bag_1000.bag_upper));

			// then all the nodes after the duplicate are lost (because it is set as the tail)
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3]);
			// also in the full iteration, 2 and 3 are from bag_1000 and 1 is from bag_10.
			assert_eq!(get_list_as_ids(), vec![2, 3, 1]);

			// and the last accessible node has an **incorrect** prev pointer.
			assert_eq!(
				Node::<Runtime>::get(&3).unwrap(),
				node(3, Some(4), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// when inserting a duplicate id of the head
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4]);
			bag_1000.insert_node_unchecked(node(2, None, None, 0));

			// then all nodes after the head are lost
			assert_eq!(bag_as_ids(&bag_1000), vec![2]);

			// and the re-fetched node has bad pointers
			assert_eq!(
				Node::<Runtime>::get(&2).unwrap(),
				node(2, Some(4), None, bag_1000.bag_upper)
			);
			//         ^^^ despite being the bags head, it has a prev

			assert_eq!(bag_1000, Bag { head: Some(2), tail: Some(2), bag_upper: 1_000 })
		});
	}

	// Panics in case of duplicate tail insert (which would result in an infinite loop).
	#[test]
	#[cfg_attr(
		debug_assertions,
		should_panic = "system logic error: inserting a node who has the id of tail"
	)]
	fn insert_node_duplicate_tail_panics_with_debug_assert() {
		ExtBuilder::default().build_and_execute(|| {
			let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };

			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])],);
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();

			// when inserting a duplicate id that is already the tail
			assert_eq!(bag_1000.tail, Some(4));
			assert_eq!(bag_1000.iter().count(), 3);
			bag_1000.insert_node_unchecked(node(4, None, None, bag_1000.bag_upper)); // panics in debug
			assert_eq!(bag_1000.iter().count(), 3); // in release we expect it to silently ignore the request.
		});
	}

	#[test]
	fn remove_node_happy_paths_works() {
		ExtBuilder::default()
			.add_ids(vec![
				(11, 10),
				(12, 10),
				(13, 1_000),
				(14, 1_000),
				(15, 2_000),
				(16, 2_000),
				(17, 2_000),
				(18, 2_000),
				(19, 2_000),
			])
			.build_and_execute_no_post_check(|| {
				let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
				let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
				let mut bag_2000 = Bag::<Runtime>::get(2_000).unwrap();

				// given
				assert_eq!(bag_as_ids(&bag_10), vec![1, 11, 12]);
				assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4, 13, 14]);
				assert_eq!(bag_as_ids(&bag_2000), vec![15, 16, 17, 18, 19]);

				// when removing a node that is not pointing at the head or tail
				let node_4 = Node::<Runtime>::get(&4).unwrap();
				let node_4_pre_remove = node_4.clone();
				bag_1000.remove_node_unchecked(&node_4);

				// then
				assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 13, 14]);
				assert_ok!(bag_1000.sanity_check());
				// and the node isn't mutated when its removed
				assert_eq!(node_4, node_4_pre_remove);

				// when removing a head that is not pointing at the tail
				let node_2 = Node::<Runtime>::get(&2).unwrap();
				bag_1000.remove_node_unchecked(&node_2);

				// then
				assert_eq!(bag_as_ids(&bag_1000), vec![3, 13, 14]);
				assert_ok!(bag_1000.sanity_check());

				// when removing a tail that is not pointing at the head
				let node_14 = Node::<Runtime>::get(&14).unwrap();
				bag_1000.remove_node_unchecked(&node_14);

				// then
				assert_eq!(bag_as_ids(&bag_1000), vec![3, 13]);
				assert_ok!(bag_1000.sanity_check());

				// when removing a tail that is pointing at the head
				let node_13 = Node::<Runtime>::get(&13).unwrap();
				bag_1000.remove_node_unchecked(&node_13);

				// then
				assert_eq!(bag_as_ids(&bag_1000), vec![3]);
				assert_ok!(bag_1000.sanity_check());

				// when removing a node that is both the head & tail
				let node_3 = Node::<Runtime>::get(&3).unwrap();
				bag_1000.remove_node_unchecked(&node_3);
				bag_1000.put(); // put into storage so `get` returns the updated bag

				// then
				assert_eq!(Bag::<Runtime>::get(1_000), None);

				// when removing a node that is pointing at both the head & tail
				let node_11 = Node::<Runtime>::get(&11).unwrap();
				bag_10.remove_node_unchecked(&node_11);

				// then
				assert_eq!(bag_as_ids(&bag_10), vec![1, 12]);
				assert_ok!(bag_10.sanity_check());

				// when removing a head that is pointing at the tail
				let node_1 = Node::<Runtime>::get(&1).unwrap();
				bag_10.remove_node_unchecked(&node_1);

				// then
				assert_eq!(bag_as_ids(&bag_10), vec![12]);
				assert_ok!(bag_10.sanity_check());
				// and since we updated the bag's head/tail, we need to write this storage so we
				// can correctly `get` it again in later checks
				bag_10.put();

				// when removing a node that is pointing at the head but not the tail
				let node_16 = Node::<Runtime>::get(&16).unwrap();
				bag_2000.remove_node_unchecked(&node_16);

				// then
				assert_eq!(bag_as_ids(&bag_2000), vec![15, 17, 18, 19]);
				assert_ok!(bag_2000.sanity_check());

				// when removing a node that is pointing at tail, but not head
				let node_18 = Node::<Runtime>::get(&18).unwrap();
				bag_2000.remove_node_unchecked(&node_18);

				// then
				assert_eq!(bag_as_ids(&bag_2000), vec![15, 17, 19]);
				assert_ok!(bag_2000.sanity_check());

				// finally, when reading from storage, the state of all bags is as expected
				assert_eq!(
					List::<Runtime>::get_bags(),
					vec![(10, vec![12]), (2_000, vec![15, 17, 19])]
				);
			});
	}

	#[test]
	fn remove_node_bad_paths_documented() {
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			let bad_upper_node_2 = Node::<Runtime> {
				id: 2,
				prev: None,
				next: Some(3),
				bag_upper: 10, // should be 1_000
			};
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();

			// when removing a node that is in the bag but has the wrong upper
			bag_1000.remove_node_unchecked(&bad_upper_node_2);
			bag_1000.put();

			// then the node is no longer in any bags
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 4])]);
			// .. and the bag it was removed from
			let bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			// is sane
			assert_ok!(bag_1000.sanity_check());
			// and has the correct head and tail.
			assert_eq!(bag_1000.head, Some(3));
			assert_eq!(bag_1000.tail, Some(4));
		});

		// Removing a node that is in another bag, will mess up that other bag.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// given a tail node is in bag 1_000
			let node_4 = Node::<Runtime>::get(&4).unwrap();

			// when we remove it from bag 10
			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			bag_10.remove_node_unchecked(&node_4);
			bag_10.put();

			// then bag remove was called on is ok,
			let bag_10 = Bag::<Runtime>::get(10).unwrap();
			assert_eq!(bag_10.tail, Some(1));
			assert_eq!(bag_10.head, Some(1));

			// but the bag that the node belonged to is in an invalid state
			let bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			// because it still has the removed node as its tail.
			assert_eq!(bag_1000.tail, Some(4));
			assert_eq!(bag_1000.head, Some(2));
		});
	}
}

mod node {
	use super::*;

	#[test]
	fn is_misplaced_works() {
		ExtBuilder::default().build_and_execute(|| {
			let node = Node::<Runtime>::get(&1).unwrap();

			// given
			assert_eq!(node.bag_upper, 10);

			// then within bag 10 its not misplaced,
			assert!(!node.is_misplaced(0));
			assert!(!node.is_misplaced(9));
			assert!(!node.is_misplaced(10));

			// and out of bag 10 it is misplaced
			assert!(node.is_misplaced(11));
		});
	}
}
