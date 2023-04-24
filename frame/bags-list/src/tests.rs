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

use frame_support::{assert_noop, assert_ok, assert_storage_noop, traits::IntegrityTest};

use super::*;
use frame_election_provider_support::{SortedListProvider, VoteWeight};
use list::Bag;
use mock::{test_utils::*, *};

mod pallet {
	use super::*;

	#[test]
	fn rebag_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (20, vec![42]), (1_000, vec![2, 3, 4])]
			);

			// when increasing score to the level of non-existent bag
			assert_eq!(List::<Runtime>::get_score(&42).unwrap(), 20);
			StakingMock::set_score_of(&42, 2_000);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 42));
			assert_eq!(List::<Runtime>::get_score(&42).unwrap(), 2_000);

			// then a new bag is created and the id moves into it
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2_000, vec![42])]
			);

			// when decreasing score within the range of the current bag
			StakingMock::set_score_of(&42, 1_001);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 42));

			// then the id does not move
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2_000, vec![42])]
			);
			// but the score is updated
			assert_eq!(List::<Runtime>::get_score(&42).unwrap(), 1_001);

			// when reducing score to the level of a non-existent bag
			StakingMock::set_score_of(&42, 30);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 42));

			// then a new bag is created and the id moves into it
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (30, vec![42]), (1_000, vec![2, 3, 4])]
			);
			assert_eq!(List::<Runtime>::get_score(&42).unwrap(), 30);

			// when increasing score to the level of a pre-existing bag
			StakingMock::set_score_of(&42, 500);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 42));

			// then the id moves into that bag
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4, 42])]
			);
			assert_eq!(List::<Runtime>::get_score(&42).unwrap(), 500);
		});
	}

	// Rebagging the tail of a bag results in the old bag having a new tail and an overall correct
	// state.
	#[test]
	fn rebag_tail_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// when
			StakingMock::set_score_of(&4, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 4));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 4]), (1_000, vec![2, 3])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(2), Some(3), 1_000));

			// when
			StakingMock::set_score_of(&3, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 3));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 4, 3]), (1_000, vec![2])]);

			assert_eq!(Bag::<Runtime>::get(10).unwrap(), Bag::new(Some(1), Some(3), 10));
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(2), Some(2), 1_000));
			assert_eq!(get_list_as_ids(), vec![2u32, 1, 4, 3]);

			// when
			StakingMock::set_score_of(&2, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 2));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 4, 3, 2])]);
			assert_eq!(Bag::<Runtime>::get(1_000), None);
		});
	}

	// Rebagging the head of a bag results in the old bag having a new head and an overall correct
	// state.
	#[test]
	fn rebag_head_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			StakingMock::set_score_of(&2, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 2));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 2]), (1_000, vec![3, 4])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(3), Some(4), 1_000));

			// when
			StakingMock::set_score_of(&3, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 3));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 2, 3]), (1_000, vec![4])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(4), Some(4), 1_000));

			// when
			StakingMock::set_score_of(&4, 10);
			assert_ok!(BagsList::rebag(RuntimeOrigin::signed(0), 4));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1, 2, 3, 4])]);
			assert_eq!(Bag::<Runtime>::get(1_000), None);
		});
	}

	#[test]
	fn wrong_rebag_errs() {
		ExtBuilder::default().build_and_execute(|| {
			let node_3 = list::Node::<Runtime>::get(&3).unwrap();
			// when account 3 is _not_ misplaced with score 500
			NextVoteWeight::set(500);
			assert!(!node_3.is_misplaced(500));

			// then calling rebag on account 3 with score 500 is a noop
			assert_storage_noop!(assert_eq!(BagsList::rebag(RuntimeOrigin::signed(0), 3), Ok(())));

			// when account 42 is not in the list
			assert!(!BagsList::contains(&42));
			// then rebag-ing account 42 is an error
			assert_storage_noop!(assert!(matches!(
				BagsList::rebag(RuntimeOrigin::signed(0), 42),
				Err(_)
			)));
		});
	}

	#[test]
	#[should_panic = "thresholds must strictly increase, and have no duplicates"]
	fn duplicate_in_bags_threshold_panics() {
		const DUPE_THRESH: &[VoteWeight; 4] = &[10, 20, 30, 30];
		BagThresholds::set(DUPE_THRESH);
		BagsList::integrity_test();
	}

	#[test]
	#[should_panic = "thresholds must strictly increase, and have no duplicates"]
	fn decreasing_in_bags_threshold_panics() {
		const DECREASING_THRESH: &[VoteWeight; 4] = &[10, 30, 20, 40];
		BagThresholds::set(DECREASING_THRESH);
		BagsList::integrity_test();
	}

	#[test]
	fn empty_threshold_works() {
		BagThresholds::set(Default::default()); // which is the same as passing `()` to `Get<_>`.
		ExtBuilder::default().build_and_execute(|| {
			// everyone in the same bag.
			assert_eq!(List::<Runtime>::get_bags(), vec![(VoteWeight::MAX, vec![1, 2, 3, 4])]);

			// any insertion goes there as well.
			assert_ok!(List::<Runtime>::insert(5, 999));
			assert_ok!(List::<Runtime>::insert(6, 0));
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(VoteWeight::MAX, vec![1, 2, 3, 4, 5, 6])]
			);

			// any rebag is noop.
			assert_storage_noop!(assert_eq!(BagsList::rebag(RuntimeOrigin::signed(0), 1), Ok(())));
		})
	}

	#[test]
	fn put_in_front_of_two_node_bag_heavier_is_tail() {
		ExtBuilder::default()
			.skip_genesis_ids()
			.add_ids(vec![(10, 15), (11, 16)])
			.build_and_execute(|| {
				// given
				assert_eq!(List::<Runtime>::get_bags(), vec![(20, vec![10, 11])]);

				// when
				assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(11), 10));

				// then
				assert_eq!(List::<Runtime>::get_bags(), vec![(20, vec![11, 10])]);
			});
	}

	#[test]
	fn put_in_front_of_two_node_bag_heavier_is_head() {
		ExtBuilder::default()
			.skip_genesis_ids()
			.add_ids(vec![(11, 16), (10, 15)])
			.build_and_execute(|| {
				// given
				assert_eq!(List::<Runtime>::get_bags(), vec![(20, vec![11, 10])]);

				// when
				assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(11), 10));

				// then
				assert_eq!(List::<Runtime>::get_bags(), vec![(20, vec![11, 10])]);
			});
	}

	#[test]
	fn put_in_front_of_non_terminal_nodes_heavier_behind() {
		ExtBuilder::default().add_ids(vec![(5, 1_000)]).build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5])]);

			StakingMock::set_score_of(&3, 999);

			// when
			assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(4), 3));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 4, 3, 5])]);
		});
	}

	#[test]
	fn put_in_front_of_non_terminal_nodes_heavier_in_front() {
		ExtBuilder::default()
			.add_ids(vec![(5, 1_000), (6, 1_000)])
			.build_and_execute(|| {
				// given
				assert_eq!(
					List::<Runtime>::get_bags(),
					vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5, 6])]
				);

				StakingMock::set_score_of(&5, 999);

				// when
				assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(3), 5));

				// then
				assert_eq!(
					List::<Runtime>::get_bags(),
					vec![(10, vec![1]), (1_000, vec![2, 4, 3, 5, 6])]
				);
			});
	}

	#[test]
	fn put_in_front_of_lighter_is_head_heavier_is_non_terminal() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			StakingMock::set_score_of(&2, 999);

			// when
			assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(3), 2));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 2, 4])]);
		});
	}

	#[test]
	fn put_in_front_of_heavier_is_tail_lighter_is_non_terminal() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			StakingMock::set_score_of(&3, 999);

			// when
			assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(4), 3));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 4, 3])]);
		});
	}

	#[test]
	fn put_in_front_of_heavier_is_tail_lighter_is_head() {
		ExtBuilder::default().add_ids(vec![(5, 1_000)]).build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5])]);

			StakingMock::set_score_of(&2, 999);

			// when
			assert_ok!(BagsList::put_in_front_of(RuntimeOrigin::signed(5), 2));

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![5, 2, 3, 4])]);
		});
	}

	#[test]
	fn put_in_front_of_heavier_is_head_lighter_is_not_terminal() {
		ExtBuilder::default().add_ids(vec![(5, 1_000)]).build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5])]);

			StakingMock::set_score_of(&4, 999);

			// when
			BagsList::put_in_front_of(RuntimeOrigin::signed(2), 4).unwrap();

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 2, 4, 5])]);
		});
	}

	#[test]
	fn put_in_front_of_lighter_is_tail_heavier_is_not_terminal() {
		ExtBuilder::default().add_ids(vec![(5, 900)]).build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 5])]);

			// when
			BagsList::put_in_front_of(RuntimeOrigin::signed(3), 5).unwrap();

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 4, 3, 5])]);
		});
	}

	#[test]
	fn put_in_front_of_lighter_is_tail_heavier_is_head() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			StakingMock::set_score_of(&4, 999);

			// when
			BagsList::put_in_front_of(RuntimeOrigin::signed(2), 4).unwrap();

			// then
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 2, 4])]);
		});
	}

	#[test]
	fn put_in_front_of_errors_if_heavier_is_less_than_lighter() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			StakingMock::set_score_of(&3, 999);

			// then
			assert_noop!(
				BagsList::put_in_front_of(RuntimeOrigin::signed(3), 2),
				crate::pallet::Error::<Runtime>::List(ListError::NotHeavier)
			);
		});
	}

	#[test]
	fn put_in_front_of_errors_if_heavier_is_equal_weight_to_lighter() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// then
			assert_noop!(
				BagsList::put_in_front_of(RuntimeOrigin::signed(3), 4),
				crate::pallet::Error::<Runtime>::List(ListError::NotHeavier)
			);
		});
	}

	#[test]
	fn put_in_front_of_errors_if_nodes_not_found() {
		// `heavier` not found
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			assert!(!ListNodes::<Runtime>::contains_key(5));

			// then
			assert_noop!(
				BagsList::put_in_front_of(RuntimeOrigin::signed(5), 4),
				crate::pallet::Error::<Runtime>::List(ListError::NodeNotFound)
			);
		});

		// `lighter` not found
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			assert!(!ListNodes::<Runtime>::contains_key(5));

			// then
			assert_noop!(
				BagsList::put_in_front_of(RuntimeOrigin::signed(4), 5),
				crate::pallet::Error::<Runtime>::List(ListError::NodeNotFound)
			);
		});
	}

	#[test]
	fn put_in_front_of_errors_if_nodes_not_in_same_bag() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);

			// then
			assert_noop!(
				BagsList::put_in_front_of(RuntimeOrigin::signed(4), 1),
				crate::pallet::Error::<Runtime>::List(ListError::NotInSameBag)
			);
		});
	}
}

mod sorted_list_provider {
	use super::*;

	#[test]
	fn iter_works() {
		ExtBuilder::default().build_and_execute(|| {
			let expected = vec![2, 3, 4, 1];
			for (i, id) in BagsList::iter().enumerate() {
				assert_eq!(id, expected[i])
			}
		});
	}

	#[test]
	fn iter_from_works() {
		ExtBuilder::default().add_ids(vec![(5, 5), (6, 15)]).build_and_execute(|| {
			// given
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1, 5]), (20, vec![6]), (1000, vec![2, 3, 4])]
			);

			assert_eq!(BagsList::iter_from(&2).unwrap().collect::<Vec<_>>(), vec![3, 4, 6, 1, 5]);
			assert_eq!(BagsList::iter_from(&3).unwrap().collect::<Vec<_>>(), vec![4, 6, 1, 5]);
			assert_eq!(BagsList::iter_from(&4).unwrap().collect::<Vec<_>>(), vec![6, 1, 5]);
			assert_eq!(BagsList::iter_from(&6).unwrap().collect::<Vec<_>>(), vec![1, 5]);
			assert_eq!(BagsList::iter_from(&1).unwrap().collect::<Vec<_>>(), vec![5]);
			assert!(BagsList::iter_from(&5).unwrap().collect::<Vec<_>>().is_empty());
			assert!(BagsList::iter_from(&7).is_err());

			assert_storage_noop!(assert!(BagsList::iter_from(&8).is_err()));
		});
	}

	#[test]
	fn count_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(BagsList::count(), 4);

			// when inserting
			assert_ok!(BagsList::on_insert(201, 0));
			// then the count goes up
			assert_eq!(BagsList::count(), 5);

			// when removing
			BagsList::on_remove(&201).unwrap();
			// then the count goes down
			assert_eq!(BagsList::count(), 4);

			// when updating
			assert_noop!(BagsList::on_update(&201, VoteWeight::MAX), ListError::NodeNotFound);
			// then the count stays the same
			assert_eq!(BagsList::count(), 4);
		});
	}

	#[test]
	fn on_insert_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			assert_ok!(BagsList::on_insert(6, 1_000));

			// then the bags
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 6])]);
			// and list correctly include the new id,
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![2, 3, 4, 6, 1]);
			// and the count is incremented.
			assert_eq!(BagsList::count(), 5);

			// when
			assert_ok!(BagsList::on_insert(7, 1_001));

			// then the bags
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4, 6]), (2_000, vec![7])]
			);
			// and list correctly include the new id,
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![7, 2, 3, 4, 6, 1]);
			// and the count is incremented.
			assert_eq!(BagsList::count(), 6);
		})
	}

	#[test]
	fn on_insert_errors_with_duplicate_id() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert!(get_list_as_ids().contains(&3));

			// then
			assert_storage_noop!(assert_eq!(
				BagsList::on_insert(3, 20).unwrap_err(),
				ListError::Duplicate
			));
		});
	}

	#[test]
	fn on_update_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (20, vec![42]), (1_000, vec![2, 3, 4])]
			);
			assert_eq!(BagsList::count(), 5);

			// when increasing score to the level of non-existent bag
			BagsList::on_update(&42, 2_000).unwrap();

			// then the bag is created with the id in it,
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2000, vec![42])]
			);
			// and the id position is updated in the list.
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![42, 2, 3, 4, 1]);

			// when decreasing score within the range of the current bag
			BagsList::on_update(&42, 1_001).unwrap();

			// then the id does not change bags,
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2000, vec![42])]
			);
			// or change position in the list.
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![42, 2, 3, 4, 1]);

			// when increasing score to the level of a non-existent bag with the max threshold
			BagsList::on_update(&42, VoteWeight::MAX).unwrap();

			// the the new bag is created with the id in it,
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (VoteWeight::MAX, vec![42])]
			);
			// and the id position is updated in the list.
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![42, 2, 3, 4, 1]);

			// when decreasing the score to a pre-existing bag
			BagsList::on_update(&42, 1_000).unwrap();

			// then id is moved to the correct bag (as the last member),
			assert_eq!(
				List::<Runtime>::get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4, 42])]
			);
			// and the id position is updated in the list.
			assert_eq!(BagsList::iter().collect::<Vec<_>>(), vec![2, 3, 4, 42, 1]);

			// since we have only called on_update, the `count` has not changed.
			assert_eq!(BagsList::count(), 5);
		});
	}

	#[test]
	fn on_remove_works() {
		let ensure_left = |id, counter| {
			assert!(!ListNodes::<Runtime>::contains_key(id));
			assert_eq!(BagsList::count(), counter);
			assert_eq!(ListNodes::<Runtime>::count(), counter);
			assert_eq!(ListNodes::<Runtime>::iter().count() as u32, counter);
		};

		ExtBuilder::default().build_and_execute(|| {
			// it is a noop removing a non-existent id
			assert!(!ListNodes::<Runtime>::contains_key(42));
			assert_noop!(BagsList::on_remove(&42), ListError::NodeNotFound);

			// when removing a node from a bag with multiple nodes
			BagsList::on_remove(&2).unwrap();

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4, 1]);
			assert_eq!(List::<Runtime>::get_bags(), vec![(10, vec![1]), (1_000, vec![3, 4])]);
			ensure_left(2, 3);

			// when removing a node from a bag with only one node
			BagsList::on_remove(&1).unwrap();

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4]);
			assert_eq!(List::<Runtime>::get_bags(), vec![(1_000, vec![3, 4])]);
			ensure_left(1, 2);

			// when removing all remaining ids
			BagsList::on_remove(&4).unwrap();
			assert_eq!(get_list_as_ids(), vec![3]);
			ensure_left(4, 1);
			BagsList::on_remove(&3).unwrap();

			// then the storage is completely cleaned up
			assert_eq!(get_list_as_ids(), Vec::<AccountId>::new());
			ensure_left(3, 0);
		});
	}

	#[test]
	fn contains_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert!(GENESIS_IDS.iter().all(|(id, _)| BagsList::contains(id)));

			let non_existent_ids = vec![&42, &666, &13];
			assert!(non_existent_ids.iter().all(|id| !BagsList::contains(id)));
		})
	}
}
