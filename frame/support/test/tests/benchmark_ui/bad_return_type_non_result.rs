use frame_benchmarking::v2::*;
#[allow(unused_imports)]
use frame_support_test::Config;

#[benchmarks]
mod benches {
	use super::*;

	#[benchmark]
	fn bench(y: Linear<1, 2>) -> String {
		let a = 2 + 2;
		#[block]
		{}
		assert_eq!(a, 4);
		String::from("test")
	}
}

fn main() {}
