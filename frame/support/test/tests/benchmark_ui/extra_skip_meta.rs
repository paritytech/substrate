use frame_support::benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark(skip_meta, skip_meta)]
	fn bench() {
		#[block]
		{}
	}
}

fn main() {}
