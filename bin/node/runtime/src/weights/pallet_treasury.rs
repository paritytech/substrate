//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_treasury::WeightInfo for WeightInfo {
	// WARNING! Some components were not used: ["u"]
	fn propose_spend() -> Weight {
		(44773000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn reject_proposal() -> Weight {
		(37437000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn approve_proposal() -> Weight {
		(12500000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn report_awesome(r: u32, ) -> Weight {
		(54176000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["r"]
	fn retract_tip() -> Weight {
		(46571000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(35854000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add((151000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn tip(t: u32, ) -> Weight {
		(26259000 as Weight)
			.saturating_add((671000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn close_tip(t: u32, ) -> Weight {
		(86316000 as Weight)
			.saturating_add((339000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn on_initialize(p: u32, ) -> Weight {
		(54640000 as Weight)
			.saturating_add((54842000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(p as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(p as Weight)))
	}
}
