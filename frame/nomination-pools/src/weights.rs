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
		0
	}
	fn claim_payout() -> Weight {
		0
	}
	fn unbond_other() -> Weight {
		0
	}
	fn pool_withdraw_unbonded() -> Weight {
		0
	}
	fn withdraw_unbonded_other() -> Weight {
		0
	}
	fn create() -> Weight {
		0
	}
	fn nominate() -> Weight {
		0
	}
}
