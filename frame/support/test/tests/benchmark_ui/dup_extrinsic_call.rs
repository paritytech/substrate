use frame_support::benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() {
		let a = 2 + 2;
		#[extrinsic_call]
		_(stuff);
		#[extrinsic_call]
		_(other_stuff);
		assert_eq!(a, 4);
	}
}

fn main() {}
