use frame_benchmarking::v2::*;
use frame_support_test::Config;
use frame_support::parameter_types;

#[benchmarks]
mod benches {
	use super::*;

	const MY_CONST: u32 = 100;

	const fn my_fn() -> u32 {
		200
	}

	parameter_types! {
		const MyConst: u32 = MY_CONST;
	}

	#[benchmark(skip_meta, extra)]
	fn bench(a: Linear<{MY_CONST * 2}, {my_fn() + MyConst::get()}>) {
		let a = 2 + 2;
		#[block]
		{}
		assert_eq!(a, 4);
	}
}

fn main() {}
