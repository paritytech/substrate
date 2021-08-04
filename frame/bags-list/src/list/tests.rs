use super::*;
use crate::{
	mock::{ext_builder::*, test_utils::*, *},
	CounterForVoters, VoterBagFor, VoterBags, VoterNodes,
};
use frame_support::{assert_ok, assert_storage_noop};

#[test]
fn basic_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		// syntactic sugar to create a raw node
		let node = |id, prev, next| Node::<Runtime> { id, prev, next, bag_upper: 0 };

		assert_eq!(CounterForVoters::<Runtime>::get(), 4);
		assert_eq!(VoterBagFor::<Runtime>::iter().count(), 4);
		assert_eq!(VoterNodes::<Runtime>::iter().count(), 4);
		assert_eq!(VoterBags::<Runtime>::iter().count(), 2);

		assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])]);

		// the state of the bags is as expected
		assert_eq!(
			VoterBags::<Runtime>::get(10).unwrap(),
			Bag::<Runtime> { head: Some(1), tail: Some(1), bag_upper: 0 }
		);
		assert_eq!(
			VoterBags::<Runtime>::get(1_000).unwrap(),
			Bag::<Runtime> { head: Some(2), tail: Some(4), bag_upper: 0 }
		);

		assert_eq!(VoterBagFor::<Runtime>::get(2).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(2).unwrap(), node(2, None, Some(3)));

		assert_eq!(VoterBagFor::<Runtime>::get(3).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(3).unwrap(), node(3, Some(2), Some(4)));

		assert_eq!(VoterBagFor::<Runtime>::get(4).unwrap(), 1000);
		assert_eq!(VoterNodes::<Runtime>::get(4).unwrap(), node(4, Some(3), None));

		assert_eq!(VoterBagFor::<Runtime>::get(1).unwrap(), 10);
		assert_eq!(VoterNodes::<Runtime>::get(1).unwrap(), node(1, None, None));

		// non-existent id does not have a storage footprint
		assert_eq!(VoterBagFor::<Runtime>::get(41), None);
		assert_eq!(VoterNodes::<Runtime>::get(41), None);

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

	// above the threshold.
	assert_eq!(notional_bag_for::<Runtime>(11), 20);

	let max_explicit_threshold = *<Runtime as Config>::BagThresholds::get().last().unwrap();
	assert_eq!(max_explicit_threshold, 10_000);
	// if the max explicit threshold is less than VoteWeight::MAX,
	assert!(VoteWeight::MAX > max_explicit_threshold);

	// anything above it will belong to the VoteWeight::MAX bag.
	assert_eq!(notional_bag_for::<Runtime>(max_explicit_threshold), max_explicit_threshold);
	assert_eq!(notional_bag_for::<Runtime>(max_explicit_threshold + 1), VoteWeight::MAX);
}

#[test]
fn remove_last_voter_in_bags_cleans_bag() {
	ExtBuilder::default().build_and_execute(|| {
		// given
		assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])]);

		// bump 1 to a bigger bag
		List::<Runtime>::remove(&1);
		List::<Runtime>::insert(1, 10_000);

		// then the bag with bound 10 is wiped from storage.
		assert_eq!(get_bags(), vec![(1_000, vec![2, 3, 4]), (10_000, vec![1])]);

		// and can be recreated again as needed.
		List::<Runtime>::insert(77, 10);
		assert_eq!(get_bags(), vec![(10, vec![77]), (1_000, vec![2, 3, 4]), (10_000, vec![1])]);
	});
}

mod voter_list {
	use super::*;

	#[test]
	fn iteration_is_semi_sorted() {
		ExtBuilder::default()
			.add_ids(vec![(5, 2_000), (6, 2_000)])
			.build_and_execute(|| {
				// given
				assert_eq!(
					get_bags(),
					vec![(10, vec![1]), (1000, vec![2, 3, 4]), (2000, vec![5, 6])]
				);

				// then
				assert_eq!(
					get_voter_list_as_ids(),
					vec![
						5, 6, // best bag
						2, 3, 4, // middle bag
						1, // last bag.
					]
				);

				// when adding a voter that has a higher weight than pre-existing voters in the bag
				List::<Runtime>::insert(7, 10);

				// then
				assert_eq!(
					get_voter_list_as_ids(),
					vec![
						5, 6, // best bag
						2, 3, 4, // middle bag
						1, 7, // last bag; new voter is last.
					]
				);
			})
	}

	/// This tests that we can `take` x voters, even if that quantity ends midway through a list.
	#[test]
	fn take_works() {
		ExtBuilder::default()
			.add_ids(vec![(5, 2_000), (6, 2_000)])
			.build_and_execute(|| {
				// given
				assert_eq!(
					get_bags(),
					vec![(10, vec![1]), (1000, vec![2, 3, 4]), (2000, vec![5, 6])]
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
			List::<Runtime>::insert(5, 1_000);

			// then
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4, 5])]);
			assert_eq!(get_voter_list_as_ids(), vec![2, 3, 4, 5, 1]);

			// when inserting into a non-existent bag
			List::<Runtime>::insert(6, 1_001);

			// then
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4, 5]), (2000, vec![6])]);
			assert_eq!(get_voter_list_as_ids(), vec![6, 2, 3, 4, 5, 1]);
		});
	}

	#[test]
	fn remove_works() {
		use crate::{CounterForVoters, VoterBags, VoterNodes};
		let ensure_left = |id, counter| {
			assert!(!VoterBagFor::<Runtime>::contains_key(id));
			assert!(!VoterNodes::<Runtime>::contains_key(id));
			assert_eq!(CounterForVoters::<Runtime>::get(), counter);
			assert_eq!(VoterBagFor::<Runtime>::iter().count() as u32, counter);
			assert_eq!(VoterNodes::<Runtime>::iter().count() as u32, counter);
		};

		ExtBuilder::default().build_and_execute(|| {
			// when removing a non-existent voter
			assert!(!VoterBagFor::<Runtime>::contains_key(42));
			assert!(!VoterNodes::<Runtime>::contains_key(42));
			List::<Runtime>::remove(&42);

			// then nothing changes
			assert_eq!(get_voter_list_as_ids(), vec![2, 3, 4, 1]);
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])]);
			assert_eq!(CounterForVoters::<Runtime>::get(), 4);

			// when removing a node from a bag with multiple nodes
			List::<Runtime>::remove(&2);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![3, 4, 1]);
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![3, 4])]);
			ensure_left(2, 3);

			// when removing a node from a bag with only one node:
			List::<Runtime>::remove(&1);

			// then
			assert_eq!(get_voter_list_as_ids(), vec![3, 4]);
			assert_eq!(get_bags(), vec![(1000, vec![3, 4])]);
			ensure_left(1, 2);
			// bag 10 is removed
			assert!(!VoterBags::<Runtime>::contains_key(10));

			// remove remaining voters to make sure storage cleans up as expected
			List::<Runtime>::remove(&3);
			ensure_left(3, 1);
			assert_eq!(get_voter_list_as_ids(), vec![4]);

			List::<Runtime>::remove(&4);
			ensure_left(4, 0);
			assert_eq!(get_voter_list_as_ids(), Vec::<AccountId>::new());

			// bags are deleted via removals
			assert_eq!(VoterBags::<Runtime>::iter().count(), 0);
		});
	}

	#[test]
	fn update_position_for_works() {
		ExtBuilder::default().build_and_execute(|| {
			// given a correctly placed account 1
			let node = Node::<Runtime>::from_id(&1).unwrap();
			assert!(!node.is_misplaced(10));

			// .. it is invalid with weight 20
			assert!(node.is_misplaced(20));

			// then updating position moves it to the correct bag
			assert_eq!(get_bags(), vec![(10, vec![1]), (1_000, vec![2, 3, 4])]);
			assert_eq!(List::<Runtime>::update_position_for(node, 20), Some((10, 20)));

			assert_eq!(get_bags(), vec![(20, vec![1]), (1_000, vec![2, 3, 4])]);

			// get the new updated node; try and update the position with no change in weight.
			let node = Node::<Runtime>::from_id(&1).unwrap();
			// TODO: we can pass a ref to node to this function as well.
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node.clone(), 20),
				None
			));

			// then move it to bag 1000 by giving it weight 500.
			assert_eq!(List::<Runtime>::update_position_for(node.clone(), 500), Some((20, 1_000)));
			assert_eq!(get_bags(), vec![(1_000, vec![2, 3, 4, 1])]);

			// moving withing that bag again is a noop
			let node = Node::<Runtime>::from_id(&1).unwrap();
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node.clone(), 750),
				None,
			));
			assert_storage_noop!(assert_eq!(
				List::<Runtime>::update_position_for(node, 1000),
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
				// @zeke TODO: why?
				assert_storage_noop!(Bag::<Runtime>::get(bag_upper));
				let bag = Bag::<Runtime>::get(bag_upper).unwrap();
				let bag_ids = bag.iter().map(|n| *n.id()).collect::<Vec<_>>();

				assert_eq!(bag, Bag::<Runtime> { head, tail, bag_upper });
				assert_eq!(bag_ids, ids);
			};

			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])]);

			// we can fetch them
			check_bag(10, Some(1), Some(1), vec![1]);
			check_bag(1000, Some(2), Some(4), vec![2, 3, 4]);

			// and all other uppers don't get bags.
			<Runtime as Config>::BagThresholds::get()
				.iter()
				.chain(iter::once(&VoteWeight::MAX))
				.filter(|bag_upper| !vec![10, 1000].contains(bag_upper))
				.for_each(|bag_upper| {
					assert_storage_noop!(assert_eq!(Bag::<Runtime>::get(*bag_upper), None));
					assert!(!VoterBags::<Runtime>::contains_key(*bag_upper));
				});

			// when we make a pre-existing bag empty
			List::<Runtime>::remove(&1);

			// then
			assert_eq!(Bag::<Runtime>::get(10), None)
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
		ExtBuilder::default().build_and_execute_no_post_check(|| {
			let node = |id, bag_upper| Node::<Runtime> { id, prev: None, next: None, bag_upper };

			// when inserting into a bag with 1 node
			let mut bag_10 = Bag::<Runtime>::get(10).unwrap();
			// (note: bags api does not care about balance or ledger)
			bag_10.insert_node(node(42, bag_10.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_10), vec![1, 42]);

			// when inserting into a bag with 3 nodes
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			bag_1000.insert_node(node(52, bag_1000.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4, 52]);

			// when inserting into a new bag
			let mut bag_20 = Bag::<Runtime>::get_or_make(20);
			bag_20.insert_node(node(62, bag_20.bag_upper));
			// then
			assert_eq!(bag_as_ids(&bag_20), vec![62]);

			// when inserting a node pointing to the accounts not in the bag
			let node_61 =
				Node::<Runtime> { id: 61, prev: Some(21), next: Some(101), bag_upper: 20 };
			bag_20.insert_node(node_61);
			// then ids are in order
			assert_eq!(bag_as_ids(&bag_20), vec![62, 61]);
			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(20, &61).unwrap(),
				Node::<Runtime> { id: 61, prev: Some(62), next: None, bag_upper: 20 }
			);

			// state of all bags is as expected
			bag_20.put(); // need to put this bag so its in the storage map
			assert_eq!(
				get_bags(),
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
			bag_1000.insert_node(node(42, Some(1), Some(1), 0));

			// then the proper perv and next is set.
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4, 42]);

			// and when the node is re-fetched all the info is correct
			assert_eq!(
				Node::<Runtime>::get(1_000, &42).unwrap(),
				node(42, Some(4), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// given 3 is in in bag_1000 (and not a tail node)
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4]);

			// when inserting a node with duplicate id 3
			bag_1000.insert_node(node(3, None, None, bag_1000.bag_upper));

			// then all the nodes after the duplicate are lost (because it is set as the tail)
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3]);
			// also in the full iteration, 2 and 3 are from the 1000 bag and 1 from bag 10.
			assert_eq!(get_voter_list_as_ids(), vec![2, 3, 1]);

			// and the last accessible node has an **incorrect** prev pointer.
			// TODO: consider doing a check on insert, it is cheap.
			assert_eq!(
				Node::<Runtime>::get(1_000, &3).unwrap(),
				node(3, Some(4), None, bag_1000.bag_upper)
			);
		});

		ExtBuilder::default().build_and_execute_no_post_check(|| {
			// when inserting a duplicate id of the head
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();
			assert_eq!(bag_as_ids(&bag_1000), vec![2, 3, 4]);
			bag_1000.insert_node(node(2, None, None, 0));

			// then all nodes after the head are lost
			assert_eq!(bag_as_ids(&bag_1000), vec![2]);

			// and the re-fetched node has bad pointers
			assert_eq!(
				Node::<Runtime>::get(1_000, &2).unwrap(),
				node(2, Some(4), None, bag_1000.bag_upper)
			);
			//         ^^^ despite being the bags head, it has a prev

			assert_eq!(bag_1000, Bag { head: Some(2), tail: Some(2), bag_upper: 1_000 })
		});
	}

	// Panics in case of duplicate tail insert (which would result in an infinite loop).
	#[test]
	#[should_panic = "system logic error: inserting a node who has the id of tail"]
	fn insert_node_duplicate_tail_panics_with_debug_assert() {
		ExtBuilder::default().build_and_execute(|| {
			let node = |id, prev, next, bag_upper| Node::<Runtime> { id, prev, next, bag_upper };

			// given
			assert_eq!(get_bags(), vec![(10, vec![1]), (1000, vec![2, 3, 4])],);
			let mut bag_1000 = Bag::<Runtime>::get(1_000).unwrap();

			// when inserting a duplicate id that is already the tail
			assert_eq!(bag_1000.tail, Some(4));
			bag_1000.insert_node(node(4, None, None, bag_1000.bag_upper)); // panics
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

	#[test]
	fn is_misplaced_works() {
		ExtBuilder::default().build_and_execute(|| {
			let node = Node::<Runtime>::get(10, &1).unwrap();

			// given
			assert_eq!(node.bag_upper, 10);

			// then
			assert!(!node.is_misplaced(0));
			assert!(!node.is_misplaced(9));
			assert!(!node.is_misplaced(10));
			assert!(node.is_misplaced(11));
		});
	}

	// TODO a test similiar to this should exist in the staking pallet
	// #[test]
	// fn voting_data_works() {
	// 	ExtBuilder::default().build_and_execute_without_check_count(|| {
	// 		let weight_of = Staking::weight_of_fn();

	// 		// add nominator with no targets
	// 		bond_nominator(42, 43, 1_000, vec![11]);

	// 		// given
	// 		assert_eq!(
	// 			get_voter_list_as_voters(),
	// 			vec![
	// 				Voter::validator(11),
	// 				Voter::validator(21),
	// 				Voter::nominator(101),
	// 				Voter::nominator(42),
	// 				Voter::validator(31),
	// 			]
	// 		);
	// 		assert_eq!(active_era(), 0);

	// 		let slashing_spans =
	// 			<Staking as crate::Store>::SlashingSpans::iter().collect::<BTreeMap<_, _>>();
	// 		assert_eq!(slashing_spans.keys().len(), 0); // no pre-existing slashing spans

	// 		let node_11 = Node::<Test>::get(10, &11).unwrap();
	// 		assert_eq!(
	// 			node_11.voting_data(&weight_of, &slashing_spans).unwrap(),
	// 			(11, 1_000, vec![11])
	// 		);

	// 		// getting data for a nominators with 0 slashed targets
	// 		let node_101 = Node::<Test>::get(1_000, &101).unwrap();
	// 		assert_eq!(
	// 			node_101.voting_data(&weight_of, &slashing_spans).unwrap(),
	// 			(101, 500, vec![11, 21])
	// 		);
	// 		let node_42 = Node::<Test>::get(10, &42).unwrap();
	// 		assert_eq!(
	// 			node_42.voting_data(&weight_of, &slashing_spans).unwrap(),
	// 			(42, 1_000, vec![11])
	// 		);

	// 		// roll ahead an era so any slashes will be after the previous nominations
	// 		start_active_era(1);

	// 		// when a validator gets a slash,
	// 		add_slash(&11);
	// 		let slashing_spans =
	// 			<Staking as crate::Store>::SlashingSpans::iter().collect::<BTreeMap<_, _>>();

	// 		assert_eq!(slashing_spans.keys().cloned().collect::<Vec<_>>(), vec![11, 42, 101]);
	// 		// then its node no longer exists
	// 		assert_eq!(
	// 			get_voter_list_as_voters(),
	// 			vec![
	// 				Voter::validator(21),
	// 				Voter::nominator(101),
	// 				Voter::nominator(42),
	// 				Voter::validator(31),
	// 			]
	// 		);
	// 		// and its nominators no longer have it as a target
	// 		let node_101 = Node::<Test>::get(10, &101).unwrap();
	// 		assert_eq!(
	// 			node_101.voting_data(&weight_of, &slashing_spans),
	// 			Some((101, 475, vec![21])),
	// 		);

	// 		let node_42 = Node::<Test>::get(10, &42).unwrap();
	// 		assert_eq!(
	// 			node_42.voting_data(&weight_of, &slashing_spans),
	// 			None, // no voting data since its 1 target has been slashed since nominating
	// 		);
	// 	});
	// }
}
