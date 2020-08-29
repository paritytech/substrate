//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{constants::RocksDbWeight as DbWeight, Weight};

use crate::WeightInfo;

impl WeightInfo for () {
	fn register_storage_key(l: u32, ) -> Weight {
		(156811000 as Weight)
			.saturating_add((23000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_storage_key(l: u32, ) -> Weight {
		(191551000 as Weight)
			.saturating_add((20000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_url(l: u32, n: u32, ) -> Weight {
		(176312000 as Weight)
			.saturating_add((64000 as Weight).saturating_mul(l as Weight))
			.saturating_add((1000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_offchain_period(l: u32, ) -> Weight {
		(194697000 as Weight)
			.saturating_add((60000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn feed_data(l: u32, ) -> Weight {
		(181679000 as Weight)
			.saturating_add((98000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn add_provider() -> Weight {
		(100169000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_provider() -> Weight {
		(111478000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
