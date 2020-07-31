//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_multisig::WeightInfo for WeightInfo {
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(13718000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(56489000 as Weight)
			.saturating_add((89000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(63881000 as Weight)
			.saturating_add((84000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(35099000 as Weight)
			.saturating_add((142000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(71128000 as Weight)
			.saturating_add((262000 as Weight).saturating_mul(s as Weight))
			.saturating_add((5000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["z"]
	fn approve_as_multi_create(s: u32, ) -> Weight {
		(55974000 as Weight)
			.saturating_add((133000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["z"]
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		(34406000 as Weight)
			.saturating_add((158000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn approve_as_multi_complete(s: u32, z: u32, ) -> Weight {
		(72572000 as Weight)
			.saturating_add((267000 as Weight).saturating_mul(s as Weight))
			.saturating_add((7000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_as_multi(s: u32, z: u32, ) -> Weight {
		(69206000 as Weight)
			.saturating_add((118000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_as_multi_store(s: u32, z: u32, ) -> Weight {
		(68947000 as Weight)
			.saturating_add((116000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
}
