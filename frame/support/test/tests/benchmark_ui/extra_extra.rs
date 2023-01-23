use frame_support::benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark(extra, extra)]
	fn bench() {
		#[block]
		{}
	}
}

fn main() {}
