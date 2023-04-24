use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;
use frame_support_test::Call;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench() {
		#[extrinsic_call]
		thing(1);
	}
}

fn main() {}
