use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};
pub struct WeightInfo;
impl pallet_treasury::WeightInfo for WeightInfo {
	fn propose_spend(u: u32, ) -> Weight {
		(41431000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn reject_proposal(u: u32, ) -> Weight {
		(34637000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn approve_proposal(u: u32, ) -> Weight {
		(11247000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn report_awesome(r: u32, ) -> Weight {
		(50450000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn retract_tip(r: u32, ) -> Weight {
		(42780000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(32730000 as Weight)
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
		(24201000 as Weight)
			.saturating_add((690000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn close_tip(t: u32, ) -> Weight {
		(79494000 as Weight)
			.saturating_add((351000 as Weight).saturating_mul(t as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn propose_bounty(u: u32, r: u32, ) -> Weight {
		(45758000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((1000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn create_sub_bounty(u: u32, r: u32, ) -> Weight {
		(88581000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((1000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(6 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn approve_bounty(u: u32, ) -> Weight {
		(13544000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn reject_bounty(u: u32, ) -> Weight {
		(43493000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn award_bounty(u: u32, ) -> Weight {
		(27083000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn claim_bounty(u: u32, ) -> Weight {
		(116783000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(5 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn cancel_bounty(u: u32, ) -> Weight {
		(65774000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(3 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn extend_bounty_expiry(u: u32, ) -> Weight {
		(25942000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn update_bounty_value_minimum() -> Weight {
		(2458000 as Weight)
			.saturating_add(DbWeight::get().reads(0 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(51875000 as Weight)
			.saturating_add((53940000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(p as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(p as Weight)))
	}
	fn on_initialize_bounties(b: u32, ) -> Weight {
		(52952000 as Weight)
			.saturating_add((54997000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(b as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(b as Weight)))
	}
}
