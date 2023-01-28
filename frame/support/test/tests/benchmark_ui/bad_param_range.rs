use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench(x: Linear<3, 1>) {
		#[block]
		{}
	}
}

fn main() {}
