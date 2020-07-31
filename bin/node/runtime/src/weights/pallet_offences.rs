//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_offences::WeightInfo for WeightInfo {
	fn report_offence_im_online(n: u32, o: u32, r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((748944000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1818136000 as Weight).saturating_mul(o as Weight))
			.saturating_add((3330728000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads((52 as Weight).saturating_mul(o as Weight)))
			.saturating_add(DbWeight::get().reads((300 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((54 as Weight).saturating_mul(o as Weight)))
			.saturating_add(DbWeight::get().writes((300 as Weight).saturating_mul(n as Weight)))
	}
	fn report_offence_grandpa(n: u32, ) -> Weight {
		(122420000 as Weight)
			.saturating_add((29409000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(14 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(10 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn report_offence_babe(n: u32, ) -> Weight {
		(123511000 as Weight)
			.saturating_add((29277000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(14 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(10 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn on_initialize(d: u32, ) -> Weight {
		(100755282000 as Weight)
			.saturating_add((411746000 as Weight).saturating_mul(d as Weight))
			.saturating_add(DbWeight::get().reads(3039 as Weight))
			.saturating_add(DbWeight::get().writes(3053 as Weight))
	}
}
