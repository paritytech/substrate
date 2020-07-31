//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_scheduler::WeightInfo for WeightInfo {
	fn schedule(s: u32, ) -> Weight {
		(28829000 as Weight)
			.saturating_add((112000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel(s: u32, ) -> Weight {
		(27921000 as Weight)
			.saturating_add((3044000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn schedule_named(s: u32, ) -> Weight {
		(36134000 as Weight)
			.saturating_add((135000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_named(s: u32, ) -> Weight {
		(30969000 as Weight)
			.saturating_add((3050000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn on_initialize(s: u32, ) -> Weight {
		(19322000 as Weight)
			.saturating_add((25415000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
}
