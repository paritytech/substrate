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


mod voter_list {
	use super::*;

	#[test]
	fn iteration_is_semi_sorted() {
		ExtBuilder::default()
		.add_ids(vec![(51, 2_000), (61, 2_000)])
		.build_and_execute(|| {
			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![51, 61])],
			);

			// then
			assert_eq!(
				get_voter_list_as_ids(),
				vec![
					51, 61, // best bag
					11, 21, 101, // middle bag
					31,  // last bag.
				]
			);

			// when adding a voter that has a higher weight than pre-existing voters in the bag
			VoterList::<Runtime>::insert(71, 10);

			// then
			assert_eq!(
				get_voter_list_as_ids(),
				vec![
					51, 61, // best bag
					11, 21, 101, // middle bag
					31,
					71, // last bag; the new voter is last, because it is order of insertion
				]
			);
		})
	}

	/// This tests that we can `take` x voters, even if that quantity ends midway through a list.
	#[test]
	fn take_works() {
		ExtBuilder::default()
		.add_ids(vec![(51, 2_000), (61, 2_000)])
		.build_and_execute(|| {
			// given
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1000, vec![11, 21, 101]), (2000, vec![51, 61])],
			);

			// when
			let iteration =
				VoterList::<Runtime>::iter().map(|node| *node.id()).take(4).collect::<Vec<_>>();

			// then
			assert_eq!(
				iteration,
				vec![
					51, 61, // best bag, fully iterated
					11, 21, // middle bag, partially iterated
				]
			);
		})
	}

	#[test]
	fn insert_works() {
		ExtBuilder::default().build_and_execute(|| {
			// when inserting into an existing bag
			VoterList::<Runtime>::insert(71, 1_000);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 71, 31]);
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101, 71])]);

			// when inserting into a non-existent bag
			VoterList::<Runtime>::insert(81, 1_001);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![81, 11, 21, 101, 71, 31]);
			assert_eq!(
				get_bags(),
				vec![(10, vec![31]), (1_000, vec![11, 21, 101, 71]), (2_000, vec![81])]
			);
		});
	}

	#[test]
	fn remove_works() {
		use crate::{CounterForVoters, VoterBags, VoterNodes};

		let check_storage = |id, counter, voters, bags| {
			assert!(!VoterBagFor::<Runtime>::contains_key(id));
			assert!(!VoterNodes::<Runtime>::contains_key(id));
			assert_eq!(CounterForVoters::<Runtime>::get(), counter);
			assert_eq!(VoterBagFor::<Runtime>::iter().count() as u32, counter);
			assert_eq!(VoterNodes::<Runtime>::iter().count() as u32, counter);
			assert_eq!(get_voter_list_as_ids(), voters);
			assert_eq!(get_bags(), bags);
		};

		ExtBuilder::default().build_and_execute(|| {
			// when removing a non-existent voter
			assert!(!VoterBagFor::<Runtime>::contains_key(42));
			assert!(!VoterNodes::<Runtime>::contains_key(42));
			VoterList::<Runtime>::remove(&42);

			// then nothing changes
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21, 101])]);
			assert_eq!(CounterForVoters::<Runtime>::get(), 4);

			// when removing a node from a bag with multiple nodes
			VoterList::<Runtime>::remove(&11);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101, 31]);
			check_storage(
				11,
				3,
				vec![21, 101, 31],                            // voter list
				vec![(10, vec![31]), (1_000, vec![21, 101])], // bags
			);

			// when removing a node from a bag with only one node:
			VoterList::<Runtime>::remove(&31);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![21, 101]);
			check_storage(
				31,
				2,
				vec![21, 101],                // voter list
				vec![(1_000, vec![21, 101])], // bags
			);
			assert!(!VoterBags::<Runtime>::contains_key(10)); // bag 10 is removed

			// remove remaining voters to make sure storage cleans up as expected
			VoterList::<Runtime>::remove(&21);
			check_storage(
				21,
				1,
				vec![101],                // voter list
				vec![(1_000, vec![101])], // bags
			);

			VoterList::<Runtime>::remove(&101);
			check_storage(
				101,
				0,
				Vec::<u32>::new(), // voter list
				vec![],            // bags
			);
			assert!(!VoterBags::<Runtime>::contains_key(1_000)); // bag 1_000 is removed

			// bags are deleted via removals
			assert_eq!(VoterBags::<Runtime>::iter().count(), 0);
		});
	}

	#[test]
	fn update_position_for_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given a correctly placed account 31
			let node_31 = Node::<Runtime>::from_id(&31).unwrap();
			assert!(!node_31.is_misplaced(10));

			// when account 31's weight becomes 20, it is then misplaced.
			let weight_20 = 20;
			assert!(node_31.is_misplaced(weight_20));

			// then updating position moves it to the correct bag
			assert_eq!(VoterList::<Runtime>::update_position_for(node_31, weight_20), Some((10, 20)));

			assert_eq!(get_bags(), vec![(20, vec![31]), (1_000, vec![11, 21, 101])]);
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);

			// and if you try and update the position with no change in weight
			let node_31 = Node::<Runtime>::from_id(&31).unwrap();
			assert_storage_noop!(assert_eq!(
				VoterList::<Runtime>::update_position_for(node_31, weight_20),
				None,
			));

			// when account 31 needs to be moved to an existing higher bag
			let weight_500 = 500;

			// then updating positions moves it to the correct bag
			let node_31 = Node::<Runtime>::from_id(&31).unwrap();
			assert_eq!(
				VoterList::<Runtime>::update_position_for(node_31, weight_500),
				Some((20, 1_000))
			);
			assert_eq!(get_bags(), vec![(1_000, vec![11, 21, 101, 31])]);
			assert_eq!(get_voter_list_as_ids(), vec![11, 21, 101, 31]);

			// when account 31 has a higher but within its current bag
			let weight_1000 = 1_000;

			// then nothing changes
			let node_31 = Node::<Runtime>::from_id(&31).unwrap();
			assert_storage_noop!(assert_eq!(
				VoterList::<Runtime>::update_position_for(node_31, weight_1000),
				None,
			));
		});
	}
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
			let node_61 =
				Node::<Runtime> { id: 61, prev: Some(21), next: Some(101), bag_upper: 20 };
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

	// Document improper ways `insert_node` may be getting used.
	#[test]
	fn insert_node_bad_paths_documented() {
		let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };
		ExtBuilder::default().build_and_execute(|| {
			// when inserting a node with both prev & next pointing at an account in the bag
			// and an incorrect bag_upper
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node(node(42, Some(11), Some(11), 0));

			// then the ids are in the correct order
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 42]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(1_000, &42).unwrap(),
				node(42, Some(101), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute(|| {
			// given 21 is in in bag_1000 (and not a tail node)
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_eq!(bag_as_ids(&bag_1000)[1], 21);

			// when inserting a node with duplicate id 21
			bag_1000.insert_node(node(21, None, None, bag_1000.bag_upper));

			// then all the nodes after the duplicate are lost (because it is set as the tail)
			assert_eq!(bag_as_ids(&bag_1000), vec![11, 21]);
			// and the re-fetched node has an **incorrect** prev pointer.
			assert_eq!(
				Node::<Runtime>::get(1_000, &21).unwrap(),
				node(21, Some(101), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute(|| {
			// when inserting a duplicate id of the head
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node(node(11, None, None, 0));

			// then all nodes after the head are lost
			assert_eq!(bag_as_ids(&bag_1000), vec![11]);
			// and the re-fetched node has bad pointers
			assert_eq!(
				Node::<Runtime>::get(1_000, &11).unwrap(),
				node(11, Some(101), None, bag_1000.bag_upper)
				//         ^^^ despite being the bags head, it has a prev
			);

			assert_eq!(bag_1000, Bag { head: Some(11), tail: Some(11), bag_upper: 1_000 })
		});
	}

	// Panics in case of duplicate tail insert (which would result in an infinite loop).
	#[test]
	#[should_panic = "system logic error: inserting a node who has the id of tail"]
	fn insert_node_duplicate_tail_panics_with_debug_assert() {
		ExtBuilder::default().build_and_execute(|| {
			let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };

			// given
			assert_eq!(get_bags(), vec![(10, vec![31]), (1000, vec![11, 21, 101])],);
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();

			// when inserting a duplicate id that is already the tail
			assert_eq!(bag_1000.tail, Some(101));
			bag_1000.insert_node(node(101, None, None, bag_1000.bag_upper)); // panics
		});
	}

	#[test]
	fn remove_node_happy_paths_works() {
		ExtBuilder::default()
			.add_ids(vec![
				(51, 1_000),
				(61, 1_000),
				(71, 10),
				(81, 10),
				(91, 2_000),
				(161, 2_000),
				(171, 2_000),
				(181, 2_000),
				(191, 2_000),
			])
			.build_and_execute(|| {
				let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
				let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
				let mut bag_2000 = Bag::<Runtime>::get(2_000).unwrap();

				// given
				assert_eq!(bag_as_ids(&bag_10), vec![31, 71, 81]);
				assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 101, 51, 61]);
				assert_eq!(bag_as_ids(&bag_2000), vec![91, 161, 171, 181, 191]);

				// remove node that is not pointing at head or tail
				let node_101 = Node::<Runtime>::get(bag_1000.bag_upper, &101).unwrap();
				let node_101_pre_remove = node_101.clone();
				bag_1000.remove_node(&node_101);
				assert_eq!(bag_as_ids(&bag_1000), vec![11, 21, 51, 61]);
				assert_ok!(bag_1000.sanity_check());
				// node isn't mutated when its removed
				assert_eq!(node_101, node_101_pre_remove);

				// remove head when its not pointing at tail
				let node_11 = Node::<Runtime>::get(bag_1000.bag_upper, &11).unwrap();
				bag_1000.remove_node(&node_11);
				assert_eq!(bag_as_ids(&bag_1000), vec![21, 51, 61]);
				assert_ok!(bag_1000.sanity_check());

				// remove tail when its not pointing at head
				let node_61 = Node::<Runtime>::get(bag_1000.bag_upper, &61).unwrap();
				bag_1000.remove_node(&node_61);
				assert_eq!(bag_as_ids(&bag_1000), vec![21, 51]);
				assert_ok!(bag_1000.sanity_check());

				// remove tail when its pointing at head
				let node_51 = Node::<Runtime>::get(bag_1000.bag_upper, &51).unwrap();
				bag_1000.remove_node(&node_51);
				assert_eq!(bag_as_ids(&bag_1000), vec![21]);
				assert_ok!(bag_1000.sanity_check());

				// remove node that is head & tail
				let node_21 = Node::<Runtime>::get(bag_1000.bag_upper, &21).unwrap();
				bag_1000.remove_node(&node_21);
				bag_1000.put(); // put into storage so get returns the updated bag
				assert_eq!(Bag::<Runtime>::get(1_000), None);

				// remove node that is pointing at head and tail
				let node_71 = Node::<Runtime>::get(bag_10.bag_upper, &71).unwrap();
				bag_10.remove_node(&node_71);
				assert_eq!(bag_as_ids(&bag_10), vec![31, 81]);
				assert_ok!(bag_10.sanity_check());

				// remove head when pointing at tail
				let node_31 = Node::<Runtime>::get(bag_10.bag_upper, &31).unwrap();
				bag_10.remove_node(&node_31);
				assert_eq!(bag_as_ids(&bag_10), vec![81]);
				assert_ok!(bag_10.sanity_check());
				bag_10.put(); // since we updated the bag's head/tail, we need to write this storage

				// remove node that is pointing at head, but not tail
				let node_161 = Node::<Runtime>::get(bag_2000.bag_upper, &161).unwrap();
				bag_2000.remove_node(&node_161);
				assert_eq!(bag_as_ids(&bag_2000), vec![91, 171, 181, 191]);
				assert_ok!(bag_2000.sanity_check());

				// remove node that is pointing at tail, but not head
				let node_181 = Node::<Runtime>::get(bag_2000.bag_upper, &181).unwrap();
				bag_2000.remove_node(&node_181);
				assert_eq!(bag_as_ids(&bag_2000), vec![91, 171, 191]);
				assert_ok!(bag_2000.sanity_check());

				// state of all bags is as expected
				assert_eq!(get_bags(), vec![(10, vec![81]), (2_000, vec![91, 171, 191])]);
			});
	}

	#[test]
	fn remove_node_bad_paths_documented() {
		ExtBuilder::default().build_and_execute(|| {
			// removing a node that is in the bag but has the wrong upper works.

			let bad_upper_node_11 = Node::<Runtime> {
				id: 11,
				prev: None,
				next: Some(21),
				bag_upper: 10, // should be 1_000
			};
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.remove_node(&bad_upper_node_11);
			bag_1000.put();

			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![21, 101])]);
			let bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_ok!(bag_1000.sanity_check());
			assert_eq!(bag_1000.head, Some(21));
			assert_eq!(bag_1000.tail, Some(101));
		});

		ExtBuilder::default().build_and_execute(|| {
			// removing a node that is in another bag, will mess up the
			// other bag.

			let node_101 = Node::<Runtime>::get(1_000, &101).unwrap();
			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			bag_10.remove_node(&node_101); // node_101 is in bag 1_000
			bag_10.put();

			// the node was removed from its actual bag, bag_1000.
			assert_eq!(get_bags(), vec![(10, vec![31]), (1_000, vec![11, 21])]);

			// the bag remove was called on is ok.
			let bag_10 = Bag::<Runtime>::get(10).unwrap();
			assert_eq!(bag_10.tail, Some(31));
			assert_eq!(bag_10.head, Some(31));

			// but the bag that the node belonged to is in an invalid state
			let bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			// because it still has the removed node as its tail.
			assert_eq!(bag_1000.tail, Some(101));
			assert_eq!(bag_1000.head, Some(11));
			assert_ok!(bag_1000.sanity_check());
		});
	}
}

mod node {
	use super::*;
}