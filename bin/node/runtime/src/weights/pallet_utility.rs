//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_utility::WeightInfo for WeightInfo {
	fn batch(c: u32, ) -> Weight {
		(16569000 as Weight)
			.saturating_add((1982000 as Weight).saturating_mul(c as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn as_derivative() -> Weight {
		(4051000 as Weight)
	}
}
