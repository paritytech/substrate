use frame_support::benchmarking::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	#[benchmark]
	fn bench(D: Linear<1, 2>) {
		#[block]
		{}
	}
}

fn main() {}
