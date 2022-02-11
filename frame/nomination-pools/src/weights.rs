use frame_support::weights::Weight;

/// Weight functions needed for pallet_bags_list.
pub trait WeightInfo {
	fn join() -> Weight;
	fn claim_payout() -> Weight;
	fn unbond_other() -> Weight;
	fn pool_withdraw_unbonded() -> Weight;
	fn withdraw_unbonded_other() -> Weight;
	fn create() -> Weight;
	fn nominate() -> Weight;
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn join() -> Weight {
		Weight::MAX
	}
	fn claim_payout() -> Weight {
		Weight::MAX
	}
	fn unbond_other() -> Weight {
		Weight::MAX
	}
	fn pool_withdraw_unbonded() -> Weight {
		Weight::MAX
	}
	fn withdraw_unbonded_other() -> Weight {
		Weight::MAX
	}
	fn create() -> Weight {
		Weight::MAX
	}
	fn nominate() -> Weight {
		Weight::MAX
	}
}
