//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc5

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_democracy::WeightInfo for WeightInfo {
	fn propose(p: u32, ) -> Weight {
		(53253000 as Weight)
			.saturating_add((117000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn second(s: u32, ) -> Weight {
		(42964000 as Weight)
			.saturating_add((231000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn vote_new(r: u32, ) -> Weight {
		(54652000 as Weight)
			.saturating_add((286000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn vote_existing(r: u32, ) -> Weight {
		(55996000 as Weight)
			.saturating_add((265000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn emergency_cancel(r: u32, ) -> Weight {
		(40907000 as Weight)
			.saturating_add((96000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn external_propose(p: u32, v: u32, ) -> Weight {
		(14687000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(p as Weight))
			.saturating_add((106000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["p"]
	fn external_propose_majority() -> Weight {
		(3337000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["p"]
	fn external_propose_default() -> Weight {
		(3363000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["p"]
	fn fast_track() -> Weight {
		(31177000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn veto_external(v: u32, ) -> Weight {
		(31709000 as Weight)
			.saturating_add((185000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_referendum(r: u32, ) -> Weight {
		(26222000 as Weight)
			.saturating_add((108000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_queued(r: u32, ) -> Weight {
		(44884000 as Weight)
			.saturating_add((3290000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn on_initialize_external(r: u32, ) -> Weight {
		(56445000 as Weight)
			.saturating_add((25574000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn on_initialize_public(r: u32, ) -> Weight {
		(78540000 as Weight)
			.saturating_add((31194000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(6 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn on_initialize_no_launch_no_maturing(r: u32, ) -> Weight {
		(72782000 as Weight)
			.saturating_add((11095000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn delegate(r: u32, ) -> Weight {
		(72940000 as Weight)
			.saturating_add((8194000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(38768000 as Weight)
			.saturating_add((8291000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals(p: u32, ) -> Weight {
		(3595000 as Weight)
			.saturating_add((102000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_preimage(b: u32, ) -> Weight {
		(47274000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(31980000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn reap_preimage(b: u32, ) -> Weight {
		(44128000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn unlock_remove(r: u32, ) -> Weight {
		(45639000 as Weight)
			.saturating_add((187000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn unlock_set(r: u32, ) -> Weight {
		(43297000 as Weight)
			.saturating_add((326000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn remove_vote(r: u32, ) -> Weight {
		(26245000 as Weight)
			.saturating_add((382000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(26349000 as Weight)
			.saturating_add((309000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn enact_proposal_execute(b: u32, ) -> Weight {
		(52298000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn enact_proposal_slash(b: u32, ) -> Weight {
		(52164000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
