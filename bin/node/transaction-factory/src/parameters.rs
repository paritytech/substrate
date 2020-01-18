
// staking bond
let destination = pallet_indices::address::Address::Id(destination.clone().into());
let amount = (*amount).into();
let reward_destination = RewardDestination::Controller;

// authorship set_uncles
let mut uncles = vec![];
let num_headers = 10; // TODO: make it configurable.
for _ in 0..num_headers {
	let header = Header::new(
		std::cmp::max(1, self.block_no()),
		H256::random(),
		H256::random(),
		genesis_hash.clone(),
		Default::default(),
	);
	uncles.push(header.clone());
}

// balances transfer
// destination
// amount

// staking validate
let validator_prefs = ValidatorPrefs { commission: Perbill::from_rational_approximation(1u32, 10u32) };

// staking nominate
let mut targets = vec![];
for _ in 0..16 {
	targets.push(destination);
}

// staking bond_extra
let balance = |minumum_balance| minimum_balance * 2; 