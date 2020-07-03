use frame_support::weights::{Weight, constants::RocksDbWeight};

pub struct WeightForBalances;
impl pallet_balances::WeightInfo for WeightForBalances {
	fn transfer(u: u32, e: u32, ) -> Weight {
		(67603000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((0 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn transfer_best_case(u: u32, e: u32, ) -> Weight {
		(36889000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((0 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn transfer_keep_alive(u: u32, e: u32, ) -> Weight {
		(47635000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((0 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn set_balance(u: u32, e: u32, ) -> Weight {
		(27400000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((0 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn set_balance_killing(u: u32, e: u32, ) -> Weight {
		(34223000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add((0 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
}

pub struct WeightForCollective;
impl pallet_collective::WeightInfo for WeightForCollective {
	fn set_members(m: u32, n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((20229000 as Weight).saturating_mul(m as Weight))
			.saturating_add((47000 as Weight).saturating_mul(n as Weight))
			.saturating_add((25614000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn execute(m: u32, b: u32, ) -> Weight {
		(24890000 as Weight)
			.saturating_add((111000 as Weight).saturating_mul(m as Weight))
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn propose_execute(m: u32, b: u32, ) -> Weight {
		(29866000 as Weight)
			.saturating_add((216000 as Weight).saturating_mul(m as Weight))
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn propose_proposed(m: u32, p: u32, b: u32, ) -> Weight {
		(55354000 as Weight)
			.saturating_add((91000 as Weight).saturating_mul(m as Weight))
			.saturating_add((461000 as Weight).saturating_mul(p as Weight))
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn vote(m: u32, ) -> Weight {
		(47319000 as Weight)
			.saturating_add((261000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
	}
	fn close_early_disapproved(m: u32, p: u32, b: u32, ) -> Weight {
		(42820000 as Weight)
			.saturating_add((244000 as Weight).saturating_mul(m as Weight))
			.saturating_add((470000 as Weight).saturating_mul(p as Weight))
			.saturating_add((2000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn close_early_approved(m: u32, p: u32, b: u32, ) -> Weight {
		(63101000 as Weight)
			.saturating_add((249000 as Weight).saturating_mul(m as Weight))
			.saturating_add((471000 as Weight).saturating_mul(p as Weight))
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn close_disapproved(m: u32, p: u32, b: u32, ) -> Weight {
		(54899000 as Weight)
			.saturating_add((210000 as Weight).saturating_mul(m as Weight))
			.saturating_add((450000 as Weight).saturating_mul(p as Weight))
			.saturating_add((0 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn close_approved(m: u32, p: u32, b: u32, ) -> Weight {
		(67950000 as Weight)
			.saturating_add((253000 as Weight).saturating_mul(m as Weight))
			.saturating_add((465000 as Weight).saturating_mul(p as Weight))
			.saturating_add((5000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(m as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
}

pub struct WeightForDemocracy;
impl pallet_democracy::WeightInfo for WeightForDemocracy {
	fn propose(p: u32, ) -> Weight {
		(48978000 as Weight)
			.saturating_add((111000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn second(s: u32, ) -> Weight {
		(39157000 as Weight)
			.saturating_add((243000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn vote_new(r: u32, ) -> Weight {
		(51582000 as Weight)
			.saturating_add((239000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn vote_existing(r: u32, ) -> Weight {
		(50641000 as Weight)
			.saturating_add((318000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn emergency_cancel(r: u32, ) -> Weight {
		(37398000 as Weight)
			.saturating_add((109000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn external_propose(p: u32, v: u32, ) -> Weight {
		(13246000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(p as Weight))
			.saturating_add((105000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(v as Weight)))
	}
	fn external_propose_majority(p: u32, ) -> Weight {
		(3009000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn external_propose_default(p: u32, ) -> Weight {
		(3016000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn fast_track(p: u32, ) -> Weight {
		(28246000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn veto_external(v: u32, ) -> Weight {
		(28713000 as Weight)
			.saturating_add((184000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(v as Weight)))
	}
	fn cancel_referendum(r: u32, ) -> Weight {
		(22291000 as Weight)
			.saturating_add((168000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn cancel_queued(r: u32, ) -> Weight {
		(39078000 as Weight)
			.saturating_add((3243000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn on_initialize_external(r: u32, ) -> Weight {
		(50941000 as Weight)
			.saturating_add((23639000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn on_initialize_public(r: u32, ) -> Weight {
		(67747000 as Weight)
			.saturating_add((28928000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn on_initialize_no_launch_no_maturing(r: u32, ) -> Weight {
		(63335000 as Weight)
			.saturating_add((10315000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn delegate(r: u32, ) -> Weight {
		(64384000 as Weight)
			.saturating_add((7687000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(36092000 as Weight)
			.saturating_add((7613000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals(p: u32, ) -> Weight {
		(3332000 as Weight)
			.saturating_add((100000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn note_preimage(b: u32, ) -> Weight {
		(43109000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(29005000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn reap_preimage(b: u32, ) -> Weight {
		(39969000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn unlock_remove(r: u32, ) -> Weight {
		(43735000 as Weight)
			.saturating_add((125000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn unlock_set(r: u32, ) -> Weight {
		(41233000 as Weight)
			.saturating_add((278000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn remove_vote(r: u32, ) -> Weight {
		(26213000 as Weight)
			.saturating_add((295000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(24634000 as Weight)
			.saturating_add((312000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn enact_proposal_execute(b: u32, ) -> Weight {
		(47294000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn enact_proposal_slash(b: u32, ) -> Weight {
		(50021000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
}

pub struct WeightForElections;
impl pallet_elections_phragmen::WeightInfo for WeightForElections {
	fn vote(u: u32, ) -> Weight {
		(67855000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn vote_update(u: u32, ) -> Weight {
		(42962000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn remove_voter(u: u32, ) -> Weight {
		(55552000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn report_defunct_voter_correct(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1702000 as Weight).saturating_mul(c as Weight))
			.saturating_add((17735000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(v as Weight)))
	}
	fn report_defunct_voter_incorrect(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1699000 as Weight).saturating_mul(c as Weight))
			.saturating_add((17707000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_candidacy(c: u32, ) -> Weight {
		(57166000 as Weight)
			.saturating_add((326000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(c as Weight)))
	}
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		(39630000 as Weight)
			.saturating_add((184000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(c as Weight)))
	}
	fn renounce_candidacy_member_runner_up(u: u32, ) -> Weight {
		(61399000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn remove_member_without_replacement(c: u32, ) -> Weight {
		(48784671000 as Weight)
			.saturating_add((726729000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(522 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(c as Weight)))
	}
	fn remove_member_with_replacement(u: u32, ) -> Weight {
		(60624000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn remove_member_wrong_refund(u: u32, ) -> Weight {
		(7251000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn on_initialize(c: u32, ) -> Weight {
		(47990383000 as Weight)
			.saturating_add((724685000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(499 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(c as Weight)))
	}
	fn phragmen(c: u32, v: u32, e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((598264000 as Weight).saturating_mul(c as Weight))
			.saturating_add((227742000 as Weight).saturating_mul(v as Weight))
			.saturating_add((7664087000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
}

pub struct WeightForIdentity;
impl pallet_identity::WeightInfo for WeightForIdentity {
	fn add_registrar(r: u32, ) -> Weight {
		(21936000 as Weight)
			.saturating_add((472000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(54641000 as Weight)
			.saturating_add((360000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1198000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
	fn set_subs(p: u32, s: u32, ) -> Weight {
		(58372000 as Weight)
			.saturating_add((2130000 as Weight).saturating_mul(p as Weight))
			.saturating_add((3028000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(102 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(52974000 as Weight)
			.saturating_add((176000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2260000 as Weight).saturating_mul(s as Weight))
			.saturating_add((733000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(56172000 as Weight)
			.saturating_add((454000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1453000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(47839000 as Weight)
			.saturating_add((335000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1445000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
	fn set_fee(r: u32, ) -> Weight {
		(8130000 as Weight)
			.saturating_add((448000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn set_account_id(r: u32, ) -> Weight {
		(9090000 as Weight)
			.saturating_add((440000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn set_fields(r: u32, ) -> Weight {
		(8175000 as Weight)
			.saturating_add((443000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(38780000 as Weight)
			.saturating_add((439000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1447000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(66163000 as Weight)
			.saturating_add((208000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2282000 as Weight).saturating_mul(s as Weight))
			.saturating_add((737000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(x as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(x as Weight)))
	}
}

pub struct WeightForImOnline;
impl pallet_im_online::WeightInfo for WeightForImOnline {
	fn heartbeat(k: u32, e: u32, ) -> Weight {
		(37688000 as Weight)
			.saturating_add((108000 as Weight).saturating_mul(k as Weight))
			.saturating_add((215000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn validate_unsigned(k: u32, e: u32, ) -> Weight {
		(69081000 as Weight)
			.saturating_add((106000 as Weight).saturating_mul(k as Weight))
			.saturating_add((304000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
	fn validate_unsigned_and_then_heartbeat(k: u32, e: u32, ) -> Weight {
		(100816000 as Weight)
			.saturating_add((212000 as Weight).saturating_mul(k as Weight))
			.saturating_add((429000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(e as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(e as Weight)))
	}
}

pub struct WeightForIndices;
impl pallet_indices::WeightInfo for WeightForIndices {
	fn claim(i: u32, ) -> Weight {
		(38723000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
	fn transfer(i: u32, ) -> Weight {
		(44738000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
	fn free(i: u32, ) -> Weight {
		(35929000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
	fn force_transfer(i: u32, ) -> Weight {
		(36778000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
	fn freeze(i: u32, ) -> Weight {
		(33193000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
}

pub struct WeightForMultisig;
impl pallet_multisig::WeightInfo for WeightForMultisig {
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(13370000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(51719000 as Weight)
			.saturating_add((137000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(58129000 as Weight)
			.saturating_add((134000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(33951000 as Weight)
			.saturating_add((138000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(64815000 as Weight)
			.saturating_add((260000 as Weight).saturating_mul(s as Weight))
			.saturating_add((6000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn approve_as_multi_create(s: u32, z: u32, ) -> Weight {
		(52033000 as Weight)
			.saturating_add((126000 as Weight).saturating_mul(s as Weight))
			.saturating_add((0 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn approve_as_multi_approve(s: u32, z: u32, ) -> Weight {
		(32146000 as Weight)
			.saturating_add((154000 as Weight).saturating_mul(s as Weight))
			.saturating_add((0 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn approve_as_multi_complete(s: u32, z: u32, ) -> Weight {
		(67604000 as Weight)
			.saturating_add((257000 as Weight).saturating_mul(s as Weight))
			.saturating_add((7000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn cancel_as_multi(s: u32, z: u32, ) -> Weight {
		(62968000 as Weight)
			.saturating_add((115000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
	fn cancel_as_multi_store(s: u32, z: u32, ) -> Weight {
		(61945000 as Weight)
			.saturating_add((120000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(z as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(z as Weight)))
	}
}

pub struct WeightForOffences;
impl pallet_offences::WeightInfo for WeightForOffences {
	fn report_offence_im_online(r: u32, o: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((777397000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1806238000 as Weight).saturating_mul(o as Weight))
			.saturating_add((3086690000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((52 as Weight).saturating_mul(o as Weight)))
			.saturating_add(RocksDbWeight::get().reads((300 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((54 as Weight).saturating_mul(o as Weight)))
			.saturating_add(RocksDbWeight::get().writes((300 as Weight).saturating_mul(n as Weight)))
	}
	fn report_offence_grandpa(r: u32, n: u32, ) -> Weight {
		(118865000 as Weight)
			.saturating_add((221000 as Weight).saturating_mul(r as Weight))
			.saturating_add((27430000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(14 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(10 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn report_offence_babe(r: u32, n: u32, ) -> Weight {
		(117377000 as Weight)
			.saturating_add((224000 as Weight).saturating_mul(r as Weight))
			.saturating_add((27355000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(14 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(10 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn on_initialize(d: u32, ) -> Weight {
		(93620225000 as Weight)
			.saturating_add((411590000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(3039 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(d as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3053 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(d as Weight)))
	}
}

pub struct WeightForProxy;
impl pallet_proxy::WeightInfo for WeightForProxy {
	fn proxy(p: u32, ) -> Weight {
		(23950000 as Weight)
			.saturating_add((149000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn add_proxy(p: u32, ) -> Weight {
		(33965000 as Weight)
			.saturating_add((187000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn remove_proxy(p: u32, ) -> Weight {
		(31028000 as Weight)
			.saturating_add((175000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn remove_proxies(p: u32, ) -> Weight {
		(29631000 as Weight)
			.saturating_add((149000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn anonymous(p: u32, ) -> Weight {
		(48182000 as Weight)
			.saturating_add((34000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
	fn kill_anonymous(p: u32, ) -> Weight {
		(31911000 as Weight)
			.saturating_add((138000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(p as Weight)))
	}
}

pub struct WeightForScheduler;
impl pallet_scheduler::WeightInfo for WeightForScheduler {
	fn schedule(s: u32, ) -> Weight {
		(27411000 as Weight)
			.saturating_add((87000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel(s: u32, ) -> Weight {
		(25647000 as Weight)
			.saturating_add((2955000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn schedule_named(s: u32, ) -> Weight {
		(34295000 as Weight)
			.saturating_add((125000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_named(s: u32, ) -> Weight {
		(29041000 as Weight)
			.saturating_add((2980000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(s as Weight)))
	}
	fn on_initialize(s: u32, ) -> Weight {
		(19467000 as Weight)
			.saturating_add((24169000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
}

pub struct WeightForSession;
impl pallet_session::WeightInfo for WeightForSession {
	fn set_keys(n: u32, ) -> Weight {
		(62706000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(n as Weight)))
	}
	fn purge_keys(n: u32, ) -> Weight {
		(44961000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(n as Weight)))
	}
}

pub struct WeightForSystem;
impl frame_system::WeightInfo for WeightForSystem {
	fn remark(b: u32, ) -> Weight {
		(1188000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn set_heap_pages(i: u32, ) -> Weight {
		(1932000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(i as Weight)))
	}
	fn set_code_without_checks(b: u32, ) -> Weight {
		(18458000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(b as Weight)))
	}
	fn set_changes_trie_config(d: u32, ) -> Weight {
		(9310000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(d as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(d as Weight)))
	}
	fn set_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((623000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_storage(i: u32, ) -> Weight {
		(2197000 as Weight)
			.saturating_add((452000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(i as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_prefix(p: u32, ) -> Weight {
		(10475000 as Weight)
			.saturating_add((912000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn suicide(n: u32, ) -> Weight {
		(27667000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(n as Weight)))
	}
}

pub struct WeightForTimestamp;
impl pallet_timestamp::WeightInfo for WeightForTimestamp {
	fn set(t: u32, ) -> Weight {
		(8345000 as Weight)
			.saturating_add((1000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn on_finalize(t: u32, ) -> Weight {
		(5228000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
}

pub struct WeightForTreasury;
impl pallet_treasury::WeightInfo for WeightForTreasury {
	fn propose_spend(u: u32, ) -> Weight {
		(40462000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn reject_proposal(u: u32, ) -> Weight {
		(34275000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn approve_proposal(u: u32, ) -> Weight {
		(11466000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
	fn report_awesome(r: u32, ) -> Weight {
		(49311000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn retract_tip(r: u32, ) -> Weight {
		(42501000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(32791000 as Weight)
			.saturating_add((2000 as Weight).saturating_mul(r as Weight))
			.saturating_add((152000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn tip(t: u32, ) -> Weight {
		(24187000 as Weight)
			.saturating_add((668000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn close_tip(t: u32, ) -> Weight {
		(78439000 as Weight)
			.saturating_add((337000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(t as Weight)))
	}
	fn on_initialize(p: u32, ) -> Weight {
		(41697000 as Weight)
			.saturating_add((52676000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(p as Weight)))
	}
}

pub struct WeightForUtility;
impl pallet_utility::WeightInfo for WeightForUtility {
	fn batch(c: u32, ) -> Weight {
		(15536000 as Weight)
			.saturating_add((1979000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(c as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(c as Weight)))
	}
	fn as_derivative(u: u32, ) -> Weight {
		(3763000 as Weight)
			.saturating_add((0 as Weight).saturating_mul(u as Weight))
			.saturating_add(RocksDbWeight::get().reads(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(u as Weight)))
			.saturating_add(RocksDbWeight::get().writes(0 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(u as Weight)))
	}
}

pub struct WeightForVesting;
impl pallet_vesting::WeightInfo for WeightForVesting {
	fn vest_locked(l: u32, ) -> Weight {
		(42775000 as Weight)
			.saturating_add((287000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(l as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(l as Weight)))
	}
	fn vest_unlocked(l: u32, ) -> Weight {
		(45652000 as Weight)
			.saturating_add((128000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(l as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(l as Weight)))
	}
	fn vest_other_locked(l: u32, ) -> Weight {
		(42338000 as Weight)
			.saturating_add((280000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(l as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(l as Weight)))
	}
	fn vest_other_unlocked(l: u32, ) -> Weight {
		(44747000 as Weight)
			.saturating_add((141000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(l as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(l as Weight)))
	}
	fn vested_transfer(l: u32, ) -> Weight {
		(87306000 as Weight)
			.saturating_add((442000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().reads((0 as Weight).saturating_mul(l as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((0 as Weight).saturating_mul(l as Weight)))
	}
}
