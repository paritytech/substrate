use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() -> Option<BenchmarkError> {
		#[block]
		{}
		assert_eq!(2 + 2, 4);
		None
	}
}

fn main() {}
