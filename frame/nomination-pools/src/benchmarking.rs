use super::*;
use crate::Pallet as Pools;
use frame_benchmarking::{account, vec, whitelist_account};
use frame_system::RawOrigin as Origin;

const USER_SEED: u32 = 0;

fn clear_storage<T: Config>() {
	BondedPools::<T>::remove_all();
	RewardPools::<T>::remove_all();
	SubPoolsStorage::<T>::remove_all();
	Delegators::<T>::remove_all();
}

fn create_funded_user_with_balance<T: Config>(
	string: &'static str,
	n: u32,
	balance: BalanceOf<T>,
) -> T::AccountId {
	let user = account(string, n, USER_SEED);
	T::Currency::make_free_balance_be(&user, balance);
	user
}

// Create a bonded pool account, bonding `balance` and giving the account `balance * 2` free
// balance.
fn create_pool_account<T: Config>(n: u32, balance: BalanceOf<T>) -> (T::AccountId, T::AccountId) {
	let pool_creator: T::AccountId =
		create_funded_user_with_balance::<T>("pool_creator", n, balance * 2u32.into());

	Pools::<T>::create(
		Origin::Signed(pool_creator.clone()).into(),
		balance,
		n as u16,
		pool_creator.clone(),
		pool_creator.clone(),
		pool_creator.clone(),
	)
	.unwrap();

	let (pool_account, _) = BondedPools::<T>::iter()
		.find(|(_, bonded_pool)| bonded_pool.depositor == pool_creator)
		.expect("pool_creator created a pool above");

	(pool_creator, pool_account)
}

struct ListScenario<T: Config> {
	/// Stash/Controller that is expected to be moved.
	origin1: T::AccountId,
	dest_weight: BalanceOf<T>,
	origin1_delegator: Option<T::AccountId>,
}

impl<T: Config> ListScenario<T> {
	/// An expensive scenario for bags-list implementation:
	///
	/// - the node to be updated (r) is the head of a bag that has at least one other node. The bag
	///   itself will need to be read and written to update its head. The node pointed to by r.next
	///   will need to be read and written as it will need to have its prev pointer updated. Note
	///   that there are two other worst case scenarios for bag removal: 1) the node is a tail and
	///   2) the node is a middle node with prev and next; all scenarios end up with the same number
	///   of storage reads and writes.
	///
	/// - the destination bag has at least one node, which will need its next pointer updated.
	///
	/// NOTE: while this scenario specifically targets a worst case for the bags-list, it should
	/// also elicit a worst case for other known `SortedListProvider` implementations; although
	/// this may not be true against unknown `SortedListProvider` implementations.
	pub(crate) fn new(
		origin_weight: BalanceOf<T>,
		is_increase: bool,
	) -> Result<Self, &'static str> {
		ensure!(!origin_weight.is_zero(), "origin weight must be greater than 0");

		if MaxPools::<T>::get().unwrap_or(0) < 3 {
			// TODO: this is due to mock config, probably best to change
			MaxPools::<T>::put(3);
		}

		// Burn the entire issuance.
		// TODO: probably don't need this
		let i = T::Currency::burn(T::Currency::total_issuance());
		sp_std::mem::forget(i);

		// create accounts with the origin weight
		let (_, pool_origin1) = create_pool_account::<T>(USER_SEED + 2, origin_weight);
		T::StakingInterface::nominate(
			pool_origin1.clone(),
			// NOTE: these don't really need to be validators.
			vec![T::Lookup::unlookup(account("random_validator", 0, USER_SEED))],
		)?;

		let (_, pool_origin2) = create_pool_account::<T>(USER_SEED + 3, origin_weight);
		T::StakingInterface::nominate(
			pool_origin2,
			vec![T::Lookup::unlookup(account("random_validator", 0, USER_SEED))].clone(),
		)?;

		// find a destination weight that will trigger the worst case scenario
		let dest_weight_as_vote =
			T::StakingInterface::weight_update_worst_case(&pool_origin1, is_increase);

		let dest_weight: BalanceOf<T> =
			dest_weight_as_vote.try_into().map_err(|_| "could not convert u64 to Balance")?;

		// create an account with the worst case destination weight
		let (_, pool_dest1) = create_pool_account::<T>(USER_SEED + 1, dest_weight);
		T::StakingInterface::nominate(
			pool_dest1,
			vec![T::Lookup::unlookup(account("random_validator", 0, USER_SEED))],
		)?;

		Ok(ListScenario { origin1: pool_origin1, dest_weight, origin1_delegator: None })
	}

	fn add_joiner(mut self, amount: BalanceOf<T>) -> Self {
		let amount = MinJoinBond::<T>::get()
			.max(T::Currency::minimum_balance())
			// max the `given` amount with minimum thresholds for account balance and joining a pool
			// to ensure 1. the user can be created and 2. can join the pool
			.max(amount);

		let joiner: T::AccountId = account("joiner", USER_SEED, 0);
		self.origin1_delegator = Some(joiner.clone());
		T::Currency::make_free_balance_be(&joiner, amount * 2u32.into());

		let current_bonded = T::StakingInterface::bonded_balance(&self.origin1).unwrap();

		// Unbond `amount` from the underlying pool account so when the delegator joins
		// we will maintain `current_bonded`
		T::StakingInterface::unbond(self.origin1.clone(), amount).unwrap();

		// Account pool points for the unbonded balance
		BondedPools::<T>::mutate(&self.origin1, |maybe_pool| {
			maybe_pool.as_mut().map(|pool| pool.points -= amount)
		});

		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), amount, self.origin1.clone())
			.unwrap();

		assert_eq!(T::StakingInterface::bonded_balance(&self.origin1).unwrap(), current_bonded);

		self
	}
}

frame_benchmarking::benchmarks! {
	join {
		clear_storage::<T>();

		let origin_weight = MinCreateBond::<T>::get().max(T::Currency::minimum_balance()) * 2u32.into();

		// setup the worst case list scenario.
		let scenario = ListScenario::<T>::new(origin_weight, true)?;
		assert_eq!(
			T::StakingInterface::bonded_balance(&scenario.origin1).unwrap(),
			origin_weight
		);


		let max_additional = scenario.dest_weight.clone() - origin_weight;
		let joiner_free = T::Currency::minimum_balance() + max_additional;

		let joiner: T::AccountId
			= create_funded_user_with_balance::<T>("joiner", 0, joiner_free);

		whitelist_account!(joiner);
	}: _(Origin::Signed(joiner.clone()), max_additional, scenario.origin1.clone())
	verify {
		assert_eq!(T::Currency::free_balance(&joiner), joiner_free - max_additional);
		assert_eq!(
			T::StakingInterface::bonded_balance(&scenario.origin1).unwrap(),
			scenario.dest_weight
		);
	}

	claim_payout {
		clear_storage::<T>();

		let origin_weight = MinCreateBond::<T>::get().max(T::Currency::minimum_balance()) * 2u32.into();
		let (depositor, pool_account) = create_pool_account::<T>(0, origin_weight);

		let reward_account = RewardPools::<T>::get(
			pool_account
		)
		.unwrap()
		.account;

		// Send funds to the reward account of the pool
		T::Currency::make_free_balance_be(&reward_account, origin_weight);

		// Sanity check
		assert_eq!(
			T::Currency::free_balance(&depositor),
			origin_weight
		);

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor.clone()))
	verify {
		assert_eq!(
			T::Currency::free_balance(&depositor),
			origin_weight * 2u32.into()
		);
		assert_eq!(
			T::Currency::free_balance(&reward_account),
			Zero::zero()
		);
	}

	unbond_other {
		clear_storage::<T>();

		// the weight the nominator will start at. The value used here is expected to be
		// significantly higher than the first position in a list (e.g. the first bag threshold).
		let origin_weight = BalanceOf::<T>::try_from(952_994_955_240_703u128)
			.map_err(|_| "balance expected to be a u128")
			.unwrap();
		let scenario = ListScenario::<T>::new(origin_weight, false)?;

		let amount = origin_weight - scenario.dest_weight.clone();

		let scenario = scenario.add_joiner(amount);

		let delegator = scenario.origin1_delegator.unwrap().clone();
	}: _(Origin::Signed(delegator.clone()), delegator.clone())
	verify {
		assert!(
			T::StakingInterface::bonded_balance(&scenario.origin1).unwrap()
			<= scenario.dest_weight.clone()
		);
	}

	// TODO: setup a withdraw unbonded kill scenario
	pool_withdraw_unbonded {
		clear_storage::<T>();

		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(T::Currency::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Add a new delegator
		let min_join_bond = MinJoinBond::<T>::get().max(T::Currency::minimum_balance());
		let joiner = create_funded_user_with_balance::<T>("joiner", 0, min_join_bond * 2u32.into());
		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), min_join_bond, pool_account.clone())
			.unwrap();

		// Sanity check join worked
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account).unwrap(

			),
			min_create_bond + min_join_bond
		);
		assert_eq!(T::Currency::free_balance(&joiner), min_join_bond);

		// Unbond the new delegator
		Pools::<T>::unbond_other(Origin::Signed(joiner.clone()).into(), joiner.clone()).unwrap();

		// Sanity check that unbond worked
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account).unwrap(),
			min_create_bond
		);
		// Set the current era
		T::StakingInterface::set_current_era(EraIndex::max_value());

		whitelist_account!(pool_account);
	}: _(Origin::Signed(pool_account.clone()), pool_account.clone(), 0)
	verify {
		// The joiners funds didn't change
		assert_eq!(T::Currency::free_balance(&joiner), min_join_bond);

		// TODO: figure out if we can check anything else. Its tricky because the free balance hasn't
		// changed and I don't we don't have an api from here to the unlocking chunks, or staking balance lock
	}

	// TODO: setup a withdraw unbonded kill scenario, make variable over slashing spans
	withdraw_unbonded_other {
		clear_storage::<T>();

		let min_create_bond = MinCreateBond::<T>::get()
			.max(T::StakingInterface::minimum_bond())
			.max(T::Currency::minimum_balance());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Add a new delegator
		let min_join_bond = MinJoinBond::<T>::get().max(T::Currency::minimum_balance());
		let joiner = create_funded_user_with_balance::<T>("joiner", 0, min_join_bond * 2u32.into());
		Pools::<T>::join(Origin::Signed(joiner.clone()).into(), min_join_bond, pool_account.clone())
			.unwrap();

		// Sanity check join worked
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account).unwrap(

			),
			min_create_bond + min_join_bond
		);
		assert_eq!(T::Currency::free_balance(&joiner), min_join_bond);

		// Unbond the new delegator
		T::StakingInterface::set_current_era(0);
		Pools::<T>::unbond_other(Origin::Signed(joiner.clone()).into(), joiner.clone()).unwrap();

		// Sanity check that unbond worked
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account).unwrap(),
			min_create_bond
		);

		// Set the current era to ensure we can withdraw unbonded funds
		T::StakingInterface::set_current_era(EraIndex::max_value());

		whitelist_account!(joiner);
	}: _(Origin::Signed(joiner.clone()), joiner.clone(), 0)
	verify {
		assert_eq!(
			T::Currency::free_balance(&joiner),
			min_join_bond * 2u32.into()
		);
	}

	create {
		log::info!("create bench");
		clear_storage::<T>();

		let min_create_bond = MinCreateBond::<T>::get().max(T::StakingInterface::minimum_bond());
		let depositor: T::AccountId = account("depositor", USER_SEED, 0);

		// Give the depositor some balance to bond
		T::Currency::make_free_balance_be(&depositor, min_create_bond * 2u32.into());

		// Make sure no pools exist as a pre-condition for our verify checks
		assert_eq!(RewardPools::<T>::count(), 0);
		assert_eq!(BondedPools::<T>::count(), 0);

		whitelist_account!(depositor);
	}: _(
			Origin::Signed(depositor.clone()),
			min_create_bond,
			0,
			depositor.clone(),
			depositor.clone(),
			depositor.clone()
		)
	verify {
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(BondedPools::<T>::count(), 1);
		let (pool_account, new_pool) = BondedPools::<T>::iter().next().unwrap();
		assert_eq!(
			new_pool,
			BondedPoolStorage {
				points: min_create_bond,
				depositor: depositor.clone(),
				root: depositor.clone(),
				nominator: depositor.clone(),
				state_toggler: depositor.clone(),
				state: PoolState::Open,
			}
		);
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account),
			Some(min_create_bond)
		);
	}

	nominate {
		log::info!("nominate bench");
		clear_storage::<T>();

		// Create a pool
		let min_create_bond = MinCreateBond::<T>::get().max(T::StakingInterface::minimum_bond());
		let (depositor, pool_account) = create_pool_account::<T>(0, min_create_bond);

		// Create some accounts to nominate. For the sake of benchmarking they don't need to be actual validators
		let validators: Vec<_> = (0..T::StakingInterface::max_nominations())
			.map(|i|
				T::Lookup::unlookup(account("stash", USER_SEED, i))
			)
			.collect();

		whitelist_account!(depositor);
	}:_(Origin::Signed(depositor.clone()), pool_account, validators)
	verify {
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(BondedPools::<T>::count(), 1);
		let (pool_account, new_pool) = BondedPools::<T>::iter().next().unwrap();
		assert_eq!(
			new_pool,
			BondedPoolStorage {
				points: min_create_bond,
				depositor: depositor.clone(),
				root: depositor.clone(),
				nominator: depositor.clone(),
				state_toggler: depositor.clone(),
				state: PoolState::Open,
			}
		);
		assert_eq!(
			T::StakingInterface::bonded_balance(&pool_account),
			Some(min_create_bond)
		);
	}
}

frame_benchmarking::impl_benchmark_test_suite!(
	Pallet,
	crate::mock::ExtBuilder::default().build(),
	crate::mock::Runtime
);
