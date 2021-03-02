#![cfg(feature = "runtime-benchmarks")]

use crate::*;

mod benchmarking {
	use super::*;
	use frame_benchmarking::{benchmarks, account, impl_benchmark_test_suite};
	use frame_system::RawOrigin;

	benchmarks!{
		// This will measure the execution time of `accumulate_dummy` for b in [1..1000] range.
		accumulate_dummy {
			let b in 1 .. 1000;
			let caller = account("caller", 0, 0);
		}: _ (RawOrigin::Signed(caller), b.into())

		// This will measure the execution time of `set_dummy` for b in [1..1000] range.
		set_dummy {
			let b in 1 .. 1000;
		}: set_dummy (RawOrigin::Root, b.into())

		// This will measure the execution time of `set_dummy` for b in [1..10] range.
		another_set_dummy {
			let b in 1 .. 10;
		}: set_dummy (RawOrigin::Root, b.into())

		// This will measure the execution time of sorting a vector.
		sort_vector {
			let x in 0 .. 10000;
			let mut m = Vec::<u32>::new();
			for i in (0..x).rev() {
				m.push(i);
			}
		}: {
			m.sort();
		}
	}

	impl_benchmark_test_suite!(Pallet, crate::tests::new_test_ext(), crate::tests::Test);
}
