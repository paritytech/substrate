use frame_support::assert_ok;

use super::*;
use frame_election_provider_support::VoterListProvider;
use list::Bag;
use mock::{ext_builder::*, test_utils::*, *};

mod extrinsics {
	use super::*;

	fn rebag_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(get_bags(), vec![(10, vec![31]), (20, vec![42]), (1000, vec![11, 21, 101])]);

			// increase vote weight and implicitly rebag to the level of non-existent bag
			set_staking_vote_weight(2_000);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 42));
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![42])]
			);

			// decrease weight within the range of the current bag
			set_staking_vote_weight(1_001);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 42));
			// does not change bags
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![42])]
			);

			// reduce weight to the level of a non-existent bag
			set_staking_vote_weight(1_001);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 42));
			// creates the bag and moves the voter into it
			assert_eq!(get_bags(), vec![(10, vec![31]), (30, vec![42]), (1000, vec![11, 21, 101])]);

			// increase weight to a pre-existing bag
			set_staking_vote_weight(1_001);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 42));
			// moves the voter to that bag
			assert_eq!(get_bags(), vec![(10, vec![31]), (1000, vec![11, 21, 101, 42])]);
		});
	}

	// Rebagging the tail of a bag results in the old bag having a new tail and an overall correct state.
	#[test]
	fn rebag_tail_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			set_staking_vote_weight(10);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 101));

			// then
			assert_eq!(get_bags(), vec![(10, vec![31, 101]), (1000, vec![11, 21])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(11), Some(21), 1_000));

			// when
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 21));

			// then
			assert_eq!(get_bags(), vec![(10, vec![31, 101, 21]), (1000, vec![11])]);
		});
	}

	// Rebagging the head of a bag results in the old bag having a new head and an overall correct state.
	#[test]
	fn rebag_head_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when
			set_staking_vote_weight(10);
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 11));

			// then
			assert_eq!(get_bags(), vec![(10, vec![31, 11]), (1000, vec![21, 101])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(21), Some(101), 1_000));

			// when
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 21));

			// then
			assert_eq!(get_bags(), vec![(10, vec![31, 11, 21]), (1000, vec![101])]);
			assert_eq!(Bag::<Runtime>::get(1_000).unwrap(), Bag::new(Some(101), Some(101), 1_000));

			// when
			assert_ok!(PalletBagsList::rebag(Origin::signed(0), 101));

			// then
			assert_eq!(get_bags(), vec![(10, vec![31, 11, 21, 101])]);
			assert_eq!(Bag::<Runtime>::get(1_000), None);
		});
	}
}

mod bags_list_voter_list_provider {
	use super::*;

	#[test]
	fn get_voters_works() {
		ExtBuilder::default().build_and_execute(|| {
			let expected = vec![11, 21, 101, 31];
			for (i, id) in BagsListVoterListProvider::<Runtime>::get_voters().enumerate() {
				assert_eq!(id, expected[i])
			}
		});
	}

	#[test]
	fn count_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 4);

			BagsListVoterListProvider::<Runtime>::on_insert(201, 0);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);

			BagsListVoterListProvider::<Runtime>::on_remove(&201);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 4);

			BagsListVoterListProvider::<Runtime>::on_remove(&31);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 3);

			BagsListVoterListProvider::<Runtime>::on_remove(&21);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 3);
		});
	}

	#[test]
	fn on_insert_works() {
		// when
		BagsListVoterListProvider::<Runtime>::on_insert(71, 1_000);

		// then
		assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101, 71])]);
		assert_eq!(
			BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
			vec![11, 21, 101, 71, 31]
		);
		assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);
		assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());

		// when
		List::<Runtime>::insert(81, 1_001);

		// then
		assert_eq!(
			BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
			vec![81, 11, 21, 101, 71, 31]
		);
		assert_eq!(
			get_bags(),
			vec![(10, vec![31]), (1_000, vec![11, 21, 101, 71]), (2_000, vec![81])]
		);
		assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 6);
		assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());
	}

	#[test]
	fn on_update_works() {
		ExtBuilder::default().add_ids(vec![(42, 20)]).build_and_execute(|| {
			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (20, vec![42]), (1_000, vec![11, 21, 101])]
			);

			// update weight to the level of non-existent bag
			BagsListVoterListProvider::<Runtime>::on_update(&42, 2_000);
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1_000, vec![11, 21, 101]), (2_000, vec![42])]
			);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				vec![42, 11, 21, 101, 31]
			);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);
			assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());

			// decrease weight within the range of the current bag
			BagsListVoterListProvider::<Runtime>::on_update(&42, 1_001);
			// does not change bags
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1_000, vec![11, 21, 101]), (2_000, vec![42])]
			);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				vec![42, 11, 21, 101, 31]
			);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);
			assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());

			// reduce weight to the level of a non-existent bag
			BagsListVoterListProvider::<Runtime>::on_update(&42, VoteWeight::MAX);
			// creates the bag and moves the voter into it
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1_000, vec![11, 21, 101]), (VoteWeight::MAX, vec![42])]
			);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				vec![42, 11, 21, 101, 31]
			);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);
			assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());

			// increase weight to a pre-existing bag
			BagsListVoterListProvider::<Runtime>::on_update(&42, 999);
			// moves the voter to that bag
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101, 42])]);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				vec![11, 21, 101, 42, 31]
			);
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), 5);
			assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());
		});
	}

	#[test]
	fn on_remove_works() {
		let check_storage = |id, counter, accounts, bags| {
			assert!(!VoterBagFor::<Runtime>::contains_key(id));
			assert!(!VoterNodes::<Runtime>::contains_key(id));
			assert_eq!(BagsListVoterListProvider::<Runtime>::count(), counter);
			assert_eq!(CounterForVoters::<Runtime>::get(), counter);
			assert_eq!(VoterBagFor::<Runtime>::iter().count() as u32, counter);
			assert_eq!(VoterNodes::<Runtime>::iter().count() as u32, counter);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				accounts
			);
			assert_eq!(get_bags(), bags);
		};

		ExtBuilder::default().build_and_execute(|| {
			// when removing a non-existent voter
			assert!(!BagsListVoterListProvider::<Runtime>::get_voters()
				.collect::<Vec<_>>()
				.contains(&42));
			assert!(!VoterNodes::<Runtime>::contains_key(42));
			BagsListVoterListProvider::<Runtime>::on_remove(&42);

			// then nothing changes
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::get_voters().collect::<Vec<_>>(),
				vec![11, 21, 101, 31]
			);
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101])]);

			// when removing a node from a bag with multiple nodes
			BagsListVoterListProvider::<Runtime>::on_remove(&11);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101, 31]);
			check_storage(
				11,
				3,
				vec![21, 101, 31],                            // list
				vec![(10, vec![31]), (1_000, vec![21, 101])], // bags
			);

			// when removing a node from a bag with only one node:
			BagsListVoterListProvider::<Runtime>::on_remove(&31);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101]);
			check_storage(
				31,
				2,
				vec![21, 101],                // list
				vec![(1_000, vec![21, 101])], // bags
			);
			assert!(!VoterBags::<Runtime>::contains_key(10)); // bag 10 is removed

			// remove remaining voters to make sure storage cleans up as expected
			BagsListVoterListProvider::<Runtime>::on_remove(&21);
			check_storage(
				21,
				1,
				vec![101],                // list
				vec![(1_000, vec![101])], // bags
			);

			BagsListVoterListProvider::<Runtime>::on_remove(&101);
			check_storage(
				101,
				0,
				Vec::<u32>::new(), // list
				vec![],            // bags
			);
			assert!(!VoterBags::<Runtime>::contains_key(1_000)); // bag 1_000 is removed

			// bags are deleted via removals
			assert_eq!(VoterBags::<Runtime>::iter().count(), 0);
		});
	}

	#[test]
	fn sanity_check_works() {
		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(BagsListVoterListProvider::<Runtime>::sanity_check());
		});

		// make sure there are no duplicates.
		ExtBuilder::default().build_and_execute(|| {
			BagsListVoterListProvider::<Runtime>::on_insert(11, 10);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::sanity_check(),
				Err("duplicate identified")
			);

		});

		// ensure count is in sync with `CounterForVoters`.
		ExtBuilder::default().build_and_execute(|| {
			crate::CounterForVoters::<Runtime>::mutate(|counter| *counter += 1);
			assert_eq!(crate::CounterForVoters::<Runtime>::get(), 5);
			assert_eq!(
				BagsListVoterListProvider::<Runtime>::sanity_check(),
				Err("iter_count != voter_count")
			);
		});
	}
}
