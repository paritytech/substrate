use frame_benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark(skip_meta, extra, bad)]
	fn bench() {
		#[block]
		{}
	}
}

fn main() {}
