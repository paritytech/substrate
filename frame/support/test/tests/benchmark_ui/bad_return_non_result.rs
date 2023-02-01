use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn bench() -> Option<String> {
		#[block]
		{}
	}
}

fn main() {}
