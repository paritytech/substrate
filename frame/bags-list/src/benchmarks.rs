// rebag {
// 		// The most expensive case for this call:
// 		//
// 		// - It doesn't matter where in the origin bag the stash lies; the number of reads and
// 		//   writes is constant. We can use the case that the stash is the only one in the origin
// 		//   bag, for simplicity.
// 		// - The destination bag is not empty, because then we need to update the `next` pointer
// 		//   of the previous node in addition to the work we do otherwise.

// 		use crate::voter_bags::{Bag, Node};

// 		let make_validator = |n: u32, balance_factor: u32| -> Result<(T::AccountId, T::AccountId), &'static str> {
// 			let (stash, controller) = create_stash_controller::<T>(n, balance_factor, Default::default())?;
// 			whitelist_account!(controller);

// 			let prefs = ValidatorPrefs::default();
// 			// bond the full value of the stash
// 			let free_balance = T::Currency::free_balance(&stash);
// 			Staking::<T>::bond_extra(RawOrigin::Signed(stash.clone()).into(), free_balance)?;
// 			Staking::<T>::validate(RawOrigin::Signed(controller.clone()).into(), prefs)?;

// 			Ok((stash, controller))
// 		};

// 		// Clean up any existing state.
// 		clear_validators_and_nominators::<T>();

// 		let thresholds = T::VoterBagThresholds::get();

// 		// stash controls the node account
// 		let bag0_thresh = thresholds[0];
// 		let (stash, controller) = make_validator(USER_SEED, bag0_thresh as u32)?;

// 		// create another validator with more stake
// 		let bag2_thresh = thresholds[2];
// 		let (other_stash, _) = make_validator(USER_SEED + 1, bag2_thresh as u32)?;

// 		// update the stash account's value/weight
// 		//
// 		// note that we have to manually update the ledger; if we were to just call
// 		// `Staking::<T>::bond_extra`, then it would implicitly rebag. We want to separate that step
// 		// so we can measure it in isolation.
// 		let other_free_balance = T::Currency::free_balance(&other_stash);
// 		T::Currency::make_free_balance_be(&stash, other_free_balance);
// 		let controller = Staking::<T>::bonded(&stash).ok_or("stash had no controller")?;
// 		let mut ledger = Staking::<T>::ledger(&controller).ok_or("controller had no ledger")?;
// 		let extra = other_free_balance.checked_sub(&ledger.total).ok_or("balance did not increase")?;
// 		ledger.total += extra;
// 		ledger.active += extra;
// 		Staking::<T>::update_ledger(&controller, &ledger);

// 		// verify preconditions
// 		let weight_of = Staking::<T>::weight_of_fn();
// 		let node = Node::<T>::from_id(&stash).ok_or("node not found for stash")?;
// 		ensure!(
// 			node.is_misplaced(&weight_of),
// 			"rebagging only makes sense when a node is misplaced",
// 		);
// 		ensure!(
// 			{
// 				let origin_bag = Bag::<T>::get(node.bag_upper).ok_or("origin bag not found")?;
// 				origin_bag.iter().count() == 1
// 			},
// 			"stash should be the only node in origin bag",
// 		);
// 		let other_node = Node::<T>::from_id(&other_stash).ok_or("node not found for other_stash")?;
// 		ensure!(!other_node.is_misplaced(&weight_of), "other stash balance never changed");
// 		ensure!(
// 			{
// 				let destination_bag = Bag::<T>::get(node.proper_bag_for()).ok_or("destination bag not found")?;
// 				destination_bag.iter().count() != 0
// 			},
// 			"destination bag should not be empty",
// 		);
// 		drop(node);

// 		// caller will call rebag
// 		let caller = whitelisted_caller();
// 		// ensure it's distinct from the other accounts
// 		ensure!(caller != stash, "caller must not be the same as the stash");
// 		ensure!(caller != controller, "caller must not be the same as the controller");
// 	}: _(RawOrigin::Signed(caller), stash.clone())
// 	verify {
// 		let node = Node::<T>::from_id(&stash).ok_or("node not found for stash")?;
// 		ensure!(!node.is_misplaced(&weight_of), "node must be in proper place after rebag");
// 	}

// 	regenerate {
// 		// number of validator intention.
// 		let v in (MAX_VALIDATORS / 2) .. MAX_VALIDATORS;
// 		// number of nominator intention.
// 		let n in (MAX_NOMINATORS / 2) .. MAX_NOMINATORS;

// 		clear_validators_and_nominators::<T>();
// 		ensure!(
// 			create_validators_with_nominators_for_era::<T>(
// 				v,
// 				n,
// 				T::MAX_NOMINATIONS as usize,
// 				true,
// 				None,
// 			).is_ok(),
// 			"creating validators and nominators failed",
// 		);
// 	}: {
// 		let migrated = VoterList::<T>::regenerate();
// 		ensure!(v + n == migrated, "didn't migrate right amount of voters");
// 	}
