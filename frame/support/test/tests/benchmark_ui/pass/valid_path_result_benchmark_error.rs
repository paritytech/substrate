use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() -> Result<(), frame_benchmarking::v2::BenchmarkError> {
		#[block]
		{}
		Ok(())
	}
}

fn main() {}
