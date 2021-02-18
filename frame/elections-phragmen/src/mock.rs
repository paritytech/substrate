use frame_support::{dispatch::Weight, weights::constants::RocksDbWeight};
use sp_std::marker::PhantomData;

use crate::WeightInfo;


pub struct MockWeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for MockWeightInfo<T> {
	fn vote_equal(_v: u32, ) -> Weight {
		unreachable!();
	}
	fn vote_more(_v: u32, ) -> Weight {
		unreachable!();
	}
	fn vote_less(_v: u32, ) -> Weight {
		unreachable!();
	}
	fn remove_voter() -> Weight {
		unreachable!();
	}
	fn submit_candidacy(_c: u32, ) -> Weight {
		unreachable!();
	}
	fn renounce_candidacy_candidate(_c: u32, ) -> Weight {
		unreachable!();
	}
	fn renounce_candidacy_members() -> Weight {
		unreachable!();
	}
	fn renounce_candidacy_runners_up() -> Weight {
		unreachable!();
	}
	fn remove_member_with_replacement() -> Weight {
		unreachable!();
	}
	fn remove_member_wrong_refund() -> Weight {
		(7_677_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
	}
	fn clean_defunct_voters(_v: u32, _d: u32, ) -> Weight {
		unreachable!();
	}
	fn election_phragmen(c: u32, v: u32, e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1 as Weight).saturating_mul(c as Weight))
			.saturating_add((1 as Weight).saturating_mul(v as Weight))
			.saturating_add((1 as Weight).saturating_mul(e as Weight))
	}
}
