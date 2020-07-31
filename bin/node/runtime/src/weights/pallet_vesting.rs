//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_vesting::WeightInfo for WeightInfo {
	fn vest_locked(l: u32, ) -> Weight {
		(48322000 as Weight)
			.saturating_add((291000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn vest_unlocked(l: u32, ) -> Weight {
		(51105000 as Weight)
			.saturating_add((125000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn vest_other_locked(l: u32, ) -> Weight {
		(47228000 as Weight)
			.saturating_add((320000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn vest_other_unlocked(l: u32, ) -> Weight {
		(50245000 as Weight)
			.saturating_add((133000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn vested_transfer(l: u32, ) -> Weight {
		(99322000 as Weight)
			.saturating_add((472000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
}
