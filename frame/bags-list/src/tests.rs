use frame_support::{assert_ok, assert_storage_noop};

use super::*;
use frame_election_provider_support::SortedListProvider;
use list::Bag;
use mock::{ext_builder::*, test_utils::*, *};

mod pallet {
	use super::*;

	#[test]
	fn rebag_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(get_bags(), vec![(10, vec![1]), (20, vec![42]), (1000, vec![2, 3, 4])]);

			// when increasing vote weight to the level of non-existent bag
			NextVoteWeight::set(2000);
			assert_ok!(BagsList::rebag(Origin::signed(0), 42));

			// then a new bag is created and the voter moves into it
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4]), (2000, vec![42])]);

			// when decreasing weight within the range of the current bag
			NextVoteWeight::set(1001);
			assert_ok!(BagsList::rebag(Origin::signed(0), 42));

			// then the voter does not move
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4]), (2000, vec![42])]);

			// when reducing weight to the level of a non-existent bag
			NextVoteWeight::set(30);
			assert_ok!(BagsList::rebag(Origin::signed(0), 42));

			// then a new bag is created and the voter moves into it
			assert_eq!(get_bags(), vec![(10, vec![1]), (30, vec![42]), (1000, vec![2, 3, 4])]);

			// when increasing weight to the level of a pre-existing bag
			NextVoteWeight::set(500);
			assert_ok!(BagsList::rebag(Origin::signed(0), 42));

			// then the voter moves into that bag
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4, 42])]);
		});
	}

	// Rebagging the tail of a bag results in the old bag having a new tail and an overall correct
	// state.
	#[test]
	fn rebag_tail_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])]);

			// when
			NextVoteWeight::set(10);
			assert_ok!(BagsList::rebag(Origin::signed(0), 4));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 4]), (1000, vec![2, 3])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(2), Some(3), 1_000));

			// when
			assert_ok!(BagsList::rebag(Origin::signed(0), 3));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 4, 3]), (1000, vec![2])]);

			assert_eq!(Bag::<Runtime>::get(10).unwrap(), Bag::new(Some(1), Some(3), 10));
			assert_eq!(Bag::<Runtime>::get(1000).unwrap(), Bag::new(Some(2), Some(2), 1000));
			assert_eq!(get_list_as_ids(), vec![2u32, 1, 4, 3]);

			// when
			assert_ok!(BagsList::rebag(Origin::signed(0), 2));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 4, 3, 2])]);
			assert_eq!(Bag::<Runtime>::get(1000), None);
		});
	}

	// Rebagging the head of a bag results in the old bag having a new head and an overall correct
	// state.
	#[test]
	fn rebag_head_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			NextVoteWeight::set(10);
			assert_ok!(BagsList::rebag(Origin::signed(0), 2));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 2]), (1000, vec![3, 4])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(3), Some(4), 1_000));

			// when
			assert_ok!(BagsList::rebag(Origin::signed(0), 3));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 2, 3]), (1000, vec![4])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(4), Some(4), 1_000));

			// when
			assert_ok!(BagsList::rebag(Origin::signed(0), 4));

			// then
			assert_eq!(get_bags(), vec![(10, vec![1, 2, 3, 4])]);
			assert_eq!(Bag::<Runtime>::get(1_000), None);
		});
	}

	#[test]
	fn wrong_rebag_is_noop() {
		ExtBuilder::default().build_and_execute(|| {
			let node_3 = list::Node::<Runtime>::get(&3).unwrap();
			// when account 3 is _not_ misplaced with weight 500
			NextVoteWeight::set(500);
			assert!(!node_3.is_misplaced(500));

			// then calling rebag on account 3 with weight 500 is a noop
			assert_storage_noop!(assert_eq!(BagsList::rebag(Origin::signed(0), 3), Ok(())));

			// when account 42 is not in the list
			assert!(!BagsList::contains(&42));

			// then rebag-ing account 42 is a noop
			assert_storage_noop!(assert_eq!(BagsList::rebag(Origin::signed(0), 42), Ok(())));
		});
	}

	#[test]
	fn duplicate_in_bags_threshold_panics() {
		todo!()
		// probably needs some UI test
	}

	#[test]
	fn decreasing_in_bags_threshold_panics() {
		todo!()
	}
}

mod sorted_list_provider {
	use super::*;

	#[test]
	fn iter_works() {
		ExtBuilder::default().build_and_execute(|| {
			let expected = vec![2, 3, 4, 1];
			for (i, id) in <BagsList as SortedListProvider<AccountId>>::iter().enumerate() {
				assert_eq!(id, expected[i])
			}
		});
	}

	#[test]
	fn count_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 4);

			// when inserting
			<BagsList as SortedListProvider<AccountId>>::on_insert(201, 0);
			// then the count goes up
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 5);

			// when removing
			<BagsList as SortedListProvider<AccountId>>::on_remove(&201);
			// then the count goes down
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 4);

			// when updating
			<BagsList as SortedListProvider<AccountId>>::on_update(&201, VoteWeight::MAX);
			// then the count stays the same
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 4);
		});
	}

	#[test]
	fn on_insert_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			<BagsList as SortedListProvider<AccountId>>::on_insert(6, 1_000);

			// then the bags
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 6])]);
			// and list correctly include the new id,
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![2, 3, 4, 6, 1]
			);
			// and the count is incremented.
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 5);

			// when
			List::<Runtime>::insert(7, 1_001);

			// then the bags
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 6]), (2000, vec![7])]);
			// and list correctly include the new id,
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![7, 2, 3, 4, 6, 1]
			);
			// and the count is incremented.
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 6);
		})
	}

	#[test]
	fn on_update_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(get_bags(), vec![(10, vec![1]), (20, vec![42]), (1_000, vec![2, 3, 4])]);
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 5);

			// when increasing weight to the level of non-existent bag
			<BagsList as SortedListProvider<AccountId>>::on_update(&42, 2_000);

			// then the bag is created with the voter in it,
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2000, vec![42])]);
			// and the id position is updated in the list.
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![42, 2, 3, 4, 1]
			);

			// when decreasing weight within the range of the current bag
			<BagsList as SortedListProvider<AccountId>>::on_update(&42, 1_001);

			// then the voter does not change bags,
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (2000, vec![42])]);
			// or change position in the list.
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![42, 2, 3, 4, 1]
			);

			// when increasing weight to the level of a non-existent bag with the max threshold
			<BagsList as SortedListProvider<AccountId>>::on_update(&42, VoteWeight::MAX);

			// the the new bag is created with the voter in it,
			assert_eq!(
				get_bags(),
				vec![(10, vec![1]), (1_000, vec![2, 3, 4]), (VoteWeight::MAX, vec![42])]
			);
			// and the id position is updated in the list.
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![42, 2, 3, 4, 1]
			);

			// when decreasing the weight to a pre-existing bag
			<BagsList as SortedListProvider<AccountId>>::on_update(&42, 1_000);

			// then voter is moved to the correct bag (as the last member),
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4, 42])]);
			// and the id position is updated in the list.
			assert_eq!(
				<BagsList as SortedListProvider<AccountId>>::iter().collect::<Vec<_>>(),
				vec![2, 3, 4, 42, 1]
			);

			// since we have only called on_update, the `count` has not changed.
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), 5);
		});
	}

	#[test]
	fn on_remove_works() {
		let ensure_left = |id, counter| {
			assert!(!VoterNodes::<Runtime>::contains_key(id));
			assert_eq!(<BagsList as SortedListProvider<AccountId>>::count(), counter);
			assert_eq!(CounterForVoters::<Runtime>::get(), counter);
			assert_eq!(VoterNodes::<Runtime>::iter().count() as u32, counter);
		};

		ExtBuilder::default().build_and_execute(|| {
			// it is a noop removing a non-existent voter
			assert!(!VoterNodes::<Runtime>::contains_key(42));
			assert_storage_noop!(BagsList::on_remove(&42));

			// when removing a node from a bag with multiple nodes
			<BagsList as SortedListProvider<AccountId>>::on_remove(&2);

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4, 1]);
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![3, 4])]);
			ensure_left(2, 3);

			// when removing a node from a bag with only one node
			<BagsList as SortedListProvider<AccountId>>::on_remove(&1);

			// then
			assert_eq!(get_list_as_ids(), vec![3, 4]);
			assert_eq!(get_bags(), vec![(1_000, vec![3, 4])]);
			ensure_left(1, 2);

			// when removing all remaining voters
			<BagsList as SortedListProvider<AccountId>>::on_remove(&4);
			assert_eq!(get_list_as_ids(), vec![3]);
			ensure_left(4, 1);
			<BagsList as SortedListProvider<AccountId>>::on_remove(&3);

			// then the storage is completely cleaned up
			assert_eq!(get_list_as_ids(), Vec::<AccountId>::new());
			ensure_left(3, 0);
		});
	}

	#[test]
	fn sanity_check_works() {
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			assert_ok!(List::<Runtime>::sanity_check());
		});

		// make sure there are no duplicates.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			<BagsList as SortedListProvider<AccountId>>::on_insert(2, 10);
			assert_eq!(List::<Runtime>::sanity_check(), Err("duplicate identified"));
		});

		// ensure count is in sync with `CounterForVoters`.
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			crate::CounterForVoters::<Runtime>::mutate(|counter| *counter += 1);
			assert_eq!(crate::CounterForVoters::<Runtime>::get(), 5);
			assert_eq!(List::<Runtime>::sanity_check(), Err("iter_count != stored_count"));
		});
	}
}
