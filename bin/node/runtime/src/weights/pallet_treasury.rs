use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};
pub struct WeightInfo;
impl pallet_treasury::WeightInfo for WeightInfo {
	fn propose_spend() -> Weight {
		(42874000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn reject_proposal() -> Weight {
		(36209000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn approve_proposal() -> Weight {
		(11868000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn report_awesome(r: u32, ) -> Weight {
		(51438000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn retract_tip(r: u32, ) -> Weight {
		(44006000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(33898000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add((156000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn tip(t: u32, ) -> Weight {
		(24311000 as Weight)
			.saturating_add((681000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn close_tip(t: u32, ) -> Weight {
		(81432000 as Weight)
			.saturating_add((342000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn propose_bounty(r: u32, ) -> Weight {
		(46943000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn create_sub_bounty(r: u32, ) -> Weight {
		(89663000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(6 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn approve_bounty() -> Weight {
		(13773000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn reject_bounty() -> Weight {
		(44349000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn award_bounty() -> Weight {
		(27629000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn claim_bounty() -> Weight {
		(119991000 as Weight)
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn cancel_bounty() -> Weight {
		(67036000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn extend_bounty_expiry() -> Weight {
		(26393000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn update_bounty_value_minimum() -> Weight {
		(2603000 as Weight)
			.saturating_add(DbWeight::get().reads(0 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(82266000 as Weight)
			.saturating_add((34325000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn on_initialize_bounties(b: u32, ) -> Weight {
		(67226000 as Weight)
			.saturating_add((52331000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((2 as Weight).saturating_mul(b as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((2 as Weight).saturating_mul(b as Weight)))
	}
}
