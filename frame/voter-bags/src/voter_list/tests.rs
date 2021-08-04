use super::*;
use crate::{
	mock::{ext_builder::*, test_utils::*, *},
	CounterForVoters, VoterBagFor, VoterBags, VoterNodes,
};
use frame_support::{assert_ok, assert_storage_noop};

#[test]
fn setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		// syntactic sugar to create a raw node
		let node = |id, prev, next| Node::<Runtime> { id, prev, next, bag_upper: 0 };

		assert_eq!(CounterForVoters::<Runtime>::get(), 4);
		assert_eq!(VoterBagFor::<Runtime>::iter().count(), 4);
		assert_eq!(VoterNodes::<Runtime>::iter().count(), 4);
		assert_eq!(VoterBags::<Runtime>::iter().count(), 2);

		// the state of the bags is as expected
		assert_eq!(
			VoterBags::<Runtime>::get(10).unwrap(),
			Bag::<Runtime> { head: Some(31), tail: Some(31), bag_upper: 0 }
		);
		assert_eq!(
			VoterBags::<Runtime>::get(1_000).unwrap(),
			Bag::<Runtime> { head: Some(11), tail: Some(101), bag_upper: 0 }
		);

		assert_eq!(VoterBagFor::<Runtime>::get(11).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(11).unwrap(), node(11, None, Some(21)));

		assert_eq!(VoterBagFor::<Runtime>::get(21).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(21).unwrap(), node(21, Some(11), Some(101)));

		assert_eq!(VoterBagFor::<Runtime>::get(31).unwrap(), 10);
		assert_eq!(VoterNodes::<Runtime>::get(31).unwrap(), node(31, None, None));

		assert_eq!(VoterBagFor::<Runtime>::get(101).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(101).unwrap(), node(101, Some(21), None));

		// non-existent id does not have a storage footprint
		assert_eq!(VoterBagFor::<Runtime>::get(41), None);
		assert_eq!(VoterNodes::<Runtime>::get(41), None);

		// iteration of the bags would yield:
		assert_eq!(
			VoterList::<Runtime>::iter().map(|n| *n.id()).collect::<Vec<_>>(),
			vec![11, 21, 101, 31],
			//   ^^ note the order of insertion in genesis!
		);

		assert_eq!(get_bags(), vec![(10, vec![31]), (1000, vec![11, 21, 101])]);
	});
}

#[test]
fn notional_bag_for_works() {
	// under a threshold gives the next threshold.
	assert_eq!(notional_bag_for::<Runtime>(0), 10);
	assert_eq!(notional_bag_for::<Runtime>(9), 10);
	assert_eq!(notional_bag_for::<Runtime>(11), 20);

	// at a threshold gives that threshold.
	assert_eq!(notional_bag_for::<Runtime>(10), 10);

	let max_explicit_threshold = *<Runtime as Config>::VoterBagThresholds::get().last().unwrap();
	assert_eq!(max_explicit_threshold, 10_000);
	// if the max explicit threshold is less than VoteWeight::MAX,
	assert!(VoteWeight::MAX > max_explicit_threshold);
	// anything above it will belong to the VoteWeight::MAX bag.
	assert_eq!(notional_bag_for::<Runtime>(max_explicit_threshold + 1), VoteWeight::MAX);
}

#[test]
fn remove_last_voter_in_bags_cleans_bag() {
	ExtBuilder::default().build_and_execute(|| {
		// given
		assert_eq!(get_bags(), vec![(10, vec![31]), (1000, vec![11, 21, 101])]);

		// Bump 31 to a bigger bag
		VoterList::<Runtime>::remove(&31);
		VoterList::<Runtime>::insert(31, 10_000);

		// then the bag with bound 10 is wiped from storage.
		assert_eq!(get_bags(), vec![(1_000, vec![11, 21, 101]), (10_000, vec![31])]);

		// and can be recreated again as needed
		VoterList::<Runtime>::insert(77, 10);
		assert_eq!(
			get_bags(),
			vec![(10, vec![77]), (1_000, vec![11, 21, 101]), (10_000, vec![31])]
		);
	});
}
mod bags {
	use super::*;

	#[test]
	fn get_works() {
		ExtBuilder::default().build_and_execute(|| {
			let check_bag = |bag_upper, head, tail, ids| {
				assert_storage_noop!(Bag::<Runtime>::get(bag_upper));

				let bag = Bag::<Runtime>::get(bag_upper).unwrap();
				let bag_ids = bag.iter().map(|n| *n.id()).collect::<Vec<_>>();

				assert_eq!(bag, Bag::<Runtime> { head, tail, bag_upper });
				assert_eq!(bag_ids, ids);
			};

			// given uppers of bags that exist.
			let existing_bag_uppers = vec![10, 1_000];

			// we can fetch them
			check_bag(existing_bag_uppers[0], Some(31), Some(31), vec![31]);
			// (getting the same bag twice has the same results)
			check_bag(existing_bag_uppers[0], Some(31), Some(31), vec![31]);
			check_bag(existing_bag_uppers[1], Some(11), Some(101), vec![11, 21, 101]);

			// and all other uppers don't get bags.
			<Runtime as Config>::VoterBagThresholds::get()
				.iter()
				.chain(iter::once(&VoteWeight::MAX))
				.filter(|bag_upper| !existing_bag_uppers.contains(bag_upper))
				.for_each(|bag_upper| {
					assert_storage_noop!(assert_eq!(Bag::<Runtime>::get(*bag_upper), None));
					assert!(!VoterBags::<Runtime>::contains_key(*bag_upper));
				});

			// when we make a pre-existing bag empty
			VoterList::<Runtime>::remove(&31);

			// then
			assert_eq!(Bag::<Runtime>::get(existing_bag_uppers[0]), None)
		});
	}

	#[test]
	#[should_panic]
	fn get_panics_with_a_bad_threshold() {
		// NOTE: panic is only expected with debug compilation
		ExtBuilder::default().build_and_execute(|| {
			Bag::<Runtime>::get(11);
		});
	}

	#[test]
	fn insert_node_happy_paths_works() {
		ExtBuilder::default().build_and_execute(|| {
			let node = |id, bag_upper| Node::<Runtime> { id, prev: None, next: None, bag_upper };

			// when inserting into a bag with 1 node
			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			// (note: bags api does not care about balance or ledger)
			bag_10.insert_node(node(42, bag_10.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_10), vec![31, 42]);

			// when inserting into a bag with 3 nodes
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node(node(52, bag_1000.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 52]);

			// when inserting into a new bag
			let mut bag_20 = Bag::<Runtime>::get_or_make(20);
			bag_20.insert_node(node(71, bag_20.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_20), vec![71]);

			// when inserting a node pointing to the accounts not in the bag
			let node_61 = Node::<Runtime> {
				id: 61,
				prev: Some(21),
				next: Some(101),
				bag_upper: 20,
			};
			bag_20.insert_node(node_61);
			// then ids are in order
			assert_eq!(bag_as_ids(&bag_20), vec![71, 61]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(20, &61).unwrap(),
				Node::<Runtime> { id: 61, prev: Some(71), next: None, bag_upper: 20 }
			);

			// state of all bags is as expected
			bag_20.put(); // need to put this bag so its in the storage map
			assert_eq!(
				get_bags(),
				vec![(10, vec![31, 42]), (20, vec![71, 61]), (1_000, vec![11, 21, 101, 52])]
			);
		});
	}


}
