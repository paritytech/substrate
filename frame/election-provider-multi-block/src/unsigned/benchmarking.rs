use super::{Pallet as UnsignedPallet, *};
use crate::{helpers, types::*};
use frame_support::ensure;

const SEED: u64 = 1;

frame_benchmarking::benchmarks! {
	// an unsigned solution is a function of the feasibility check of single page.
	submit_unsigned {
		let v in 4000 .. 8000;
		let t in 500 .. 2000;
		let a in 5000 .. 7000;
		let d in 700 .. 1500;

		// make the snapshot

		//
	}: {} verify {}
}

frame_benchmarking::impl_benchmark_test_suite!(
	UnsignedPallet,
	crate::mock::ExtBuilder::default().build_offchainify(10).0,
	crate::mock::Runtime,
);
