use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benchmarks {
	use super::*;

	fn something() -> BenchmarkResult {
		Ok(())
	}

	#[benchmark]
	fn bench() {
		something()?;
		#[block]
		{}
	}
}

fn main() {}
