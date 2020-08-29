//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

use crate::WeightInfo;

impl WeightInfo for () {
	fn register_storage_key(l: u32, ) -> Weight {
		(188433000 as Weight)
			.saturating_add((449000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_storage_key(l: u32, ) -> Weight {
		(229551000 as Weight)
			.saturating_add((221000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_url(l: u32, n: u32, ) -> Weight {
		(102079000 as Weight)
			.saturating_add((687000 as Weight).saturating_mul(l as Weight))
			.saturating_add((22000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn feed_data(l: u32, ) -> Weight {
		(223137000 as Weight)
			.saturating_add((385000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn add_provider() -> Weight {
		(135062000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_provider() -> Weight {
		(149293000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
