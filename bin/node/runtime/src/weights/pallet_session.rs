//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_session::WeightInfo for WeightInfo {
	// WARNING! Some components were not used: ["n"]
	fn set_keys() -> Weight {
		(67501000 as Weight)
			.saturating_add(DbWeight::get().reads(7 as Weight))
			.saturating_add(DbWeight::get().writes(6 as Weight))
	}
	// WARNING! Some components were not used: ["n"]
	fn purge_keys() -> Weight {
		(47185000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(6 as Weight))
	}
	fn check_membership_proof_current_session(n: u32, ) -> Weight {
		(43531000 as Weight)
			.saturating_add((174000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
	}
	fn check_membership_proof_historical_session(n: u32, ) -> Weight {
		(69169000 as Weight)
			.saturating_add((89000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
	}
}
