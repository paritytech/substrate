use frame_support::benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() {
		let a = 2 + 2;
		#[block]
		{}
		#[block]
		{}
		assert_eq!(a, 4);
	}
}

fn main() {}
