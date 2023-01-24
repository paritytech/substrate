use frame_support::benchmarking::*;
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark(skip_meta, extra)]
	fn bench() {
		let a = 2 + 2;
		#[block]
		{}
		assert_eq!(a, 4);
	}
}

fn main() {}
