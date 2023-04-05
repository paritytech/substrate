//! Benchmarking setup for pallet-template

use super::*;

#[allow(unused)]
use crate::Pallet as Template;
use frame_benchmarking::{impl_benchmark_test_suite, whitelisted_caller, v2::*};
use frame_system::RawOrigin;

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn do_something(s: Linear<0, 100>) {
		let caller: T::AccountId = whitelisted_caller();

		#[extrinsic_call]
	 	_(RawOrigin::Signed(caller), s);
	
		assert_eq!(Something::<T>::get(), Some(s));
	}

	impl_benchmark_test_suite!(Template, crate::mock::new_test_ext(), crate::mock::Test);
}
