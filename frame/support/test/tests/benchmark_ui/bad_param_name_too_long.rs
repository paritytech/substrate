use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benchmarks {
	#[benchmark]
	fn bench(xx: Linear<1, 2>) {
		#[block]
		{}
	}
}

fn main() {}
