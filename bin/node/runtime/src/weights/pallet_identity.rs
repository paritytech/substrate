//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_identity::WeightInfo for WeightInfo {
	fn add_registrar(r: u32, ) -> Weight {
		(24115000 as Weight)
			.saturating_add((496000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(59509000 as Weight)
			.saturating_add((350000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1272000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_subs(p: u32, s: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((4144000 as Weight).saturating_mul(p as Weight))
			.saturating_add((9176000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(DbWeight::get().writes(102 as Weight))
	}
	fn add_sub(p: u32, ) -> Weight {
		(61031000 as Weight)
			.saturating_add((252000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn rename_sub(p: u32, ) -> Weight {
		(20468000 as Weight)
			.saturating_add((84000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn remove_sub(p: u32, ) -> Weight {
		(58422000 as Weight)
			.saturating_add((234000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn quit_sub(p: u32, ) -> Weight {
		(39623000 as Weight)
			.saturating_add((223000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(53751000 as Weight)
			.saturating_add((220000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2513000 as Weight).saturating_mul(s as Weight))
			.saturating_add((794000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(60879000 as Weight)
			.saturating_add((481000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1538000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(52370000 as Weight)
			.saturating_add((309000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1517000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_fee(r: u32, ) -> Weight {
		(9114000 as Weight)
			.saturating_add((456000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_account_id(r: u32, ) -> Weight {
		(10231000 as Weight)
			.saturating_add((465000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_fields(r: u32, ) -> Weight {
		(9244000 as Weight)
			.saturating_add((456000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(41890000 as Weight)
			.saturating_add((445000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1530000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(65780000 as Weight)
			.saturating_add((285000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2529000 as Weight).saturating_mul(s as Weight))
			.saturating_add((798000 as Weight).saturating_mul(x as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
}
