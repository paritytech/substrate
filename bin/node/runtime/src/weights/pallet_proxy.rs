//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_proxy::WeightInfo for WeightInfo {
	fn proxy(p: u32, ) -> Weight {
		(26181000 as Weight)
			.saturating_add((147000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
	}
	fn add_proxy(p: u32, ) -> Weight {
		(37302000 as Weight)
			.saturating_add((200000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_proxy(p: u32, ) -> Weight {
		(34069000 as Weight)
			.saturating_add((187000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_proxies(p: u32, ) -> Weight {
		(32827000 as Weight)
			.saturating_add((150000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn anonymous(p: u32, ) -> Weight {
		(53118000 as Weight)
			.saturating_add((47000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_anonymous(p: u32, ) -> Weight {
		(34854000 as Weight)
			.saturating_add((154000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
