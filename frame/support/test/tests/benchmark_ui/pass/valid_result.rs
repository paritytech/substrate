use frame_benchmarking::v2::*;
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() -> Result<bool, BenchmarkError> {
		let a = 2 + 2;
		#[block]
		{}
		assert_eq!(a, 4);
		Ok(false)
	}
}

fn main() {}
