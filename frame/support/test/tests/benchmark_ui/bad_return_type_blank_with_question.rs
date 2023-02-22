use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	fn something() -> Result<(), BenchmarkError> {
		Ok(())
	}

	#[benchmark]
	fn bench() {
		something()?;
		#[block]
		{}
		assert_eq!(2 + 2, 4);
	}
}

fn main() {}
