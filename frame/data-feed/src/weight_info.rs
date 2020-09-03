//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{constants::RocksDbWeight as DbWeight, Weight};

pub trait WeightInfo {
	fn register_storage_key(n: u32, ) -> Weight;
	fn remove_storage_key(n: u32, ) -> Weight;
	fn set_offchain_request_info(n: u32, l: u32, m: u32, ) -> Weight;
	fn set_offchain_period(n: u32, ) -> Weight;
	fn feed_data(n: u32, ) -> Weight;
	fn add_provider() -> Weight;
	fn remove_provider() -> Weight;
}


impl WeightInfo for () {
	fn register_storage_key(n: u32, ) -> Weight {
		(161740000 as Weight)
			.saturating_add((27000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_storage_key(n: u32, ) -> Weight {
		(193310000 as Weight)
			.saturating_add((186000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_offchain_request_info(n: u32, l: u32, m: u32, ) -> Weight {
		(185375000 as Weight)
			.saturating_add((255000 as Weight).saturating_mul(n as Weight))
			.saturating_add((2000 as Weight).saturating_mul(l as Weight))
			.saturating_add((2000 as Weight).saturating_mul(m as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_offchain_period(n: u32, ) -> Weight {
		(209604000 as Weight)
			.saturating_add((292000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn feed_data(n: u32, ) -> Weight {
		(252761000 as Weight)
			.saturating_add((292000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn add_provider() -> Weight {
		(99828000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_provider() -> Weight {
		(137988000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
}
