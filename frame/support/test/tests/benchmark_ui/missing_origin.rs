use frame_benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() {
		#[extrinsic_call]
		thing();
	}
}

fn main() {}
