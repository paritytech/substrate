//! Benchmarks for the bags list pallet.

use super::*;
use frame_benchmarking::{account, benchmarks};


benchmarks! {
	rebag {
		// The most expensive case for this rebag-ing:
		//
		// - The node to be rebagged should exist as a non-terminal node in a bag with at least
		//   2 other nodes so both its prev and next are nodes that will need be updated
		//   when it is removed.
		//   TODO once we optimize for not writing the bag being removed we will have the case
		//    of removing head/tail from a bag with at least 2 nodes
		// - The destination bag is not empty, because then we need to update the `next` pointer
		//   of the previous node in addition to the work we do otherwise.

		let origin_bag_thresh = 10;
		let dest_bag_thresh = 1_000;

		let origin_head = account("origin")

		Pallet::<T>::on_insert(42, )
	}
}

