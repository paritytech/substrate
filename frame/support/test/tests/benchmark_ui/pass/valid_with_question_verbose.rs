use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benchmarks {
	use super::*;

	fn something() -> Result<(), BenchmarkError> {
		Ok(())
	}

	#[benchmark]
	fn bench() -> Result<(), BenchmarkError> {
		something()?;
		#[block]
		{}
	}
}

fn main() {}
