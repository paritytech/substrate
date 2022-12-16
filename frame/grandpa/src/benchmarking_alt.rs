#![cfg(any(feature = "runtime-benchmarks", test))]

use super::{Pallet as Grandpa, *};
use frame_benchmarking::benchmarks;
use frame_system::RawOrigin;
use sp_core::H256;

frame_support::benchmarks! {
	#[frame_support::benchmark]
	fn bench_name(x: LinearComponent<0, MAX_X>, y: LinearComponent<0, MAX_Y>) {
		// Setup code
		let z = x + y;
		let caller = whitelisted_caller();
		// The extrinsic call.
		#[extrinsic_call]
		extrinsic_name(z, other_arguments);
		// Post condition verification
		assert_eq!(MyPallet::<T>::my_var(), == z);
	}
}
