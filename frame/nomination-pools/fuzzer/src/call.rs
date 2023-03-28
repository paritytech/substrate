// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Running
//! Running this fuzzer can be done with `cargo hfuzz run call`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug per_thing_rational hfuzz_workspace/call/*.fuzz`.

use frame_support::{
	assert_ok,
	traits::{Currency, GetCallName, UnfilteredDispatchable},
};
use honggfuzz::fuzz;
use pallet_nomination_pools::{
	log,
	mock::*,
	pallet as pools,
	pallet::{BondedPools, Call as PoolsCall, Event as PoolsEvents, PoolMembers},
	BondExtra, BondedPool, GlobalMaxCommission, LastPoolId, MaxPoolMembers, MaxPoolMembersPerPool,
	MaxPools, MinCreateBond, MinJoinBond, PoolId,
};
use rand::{seq::SliceRandom, Rng};
use sp_runtime::{assert_eq_error_rate, Perbill, Perquintill};

const ERA: BlockNumber = 1000;
const MAX_ED_MULTIPLE: Balance = 10_000;
const MIN_ED_MULTIPLE: Balance = 10;

// not quite elegant, just to make it available in random_signed_origin.
const REWARD_AGENT_ACCOUNT: AccountId = 42;

/// Grab random accounts, either known ones, or new ones.
fn random_signed_origin<R: Rng>(rng: &mut R) -> (RuntimeOrigin, AccountId) {
	let count = PoolMembers::<T>::count();
	if rng.gen::<bool>() && count > 0 {
		// take an existing account.
		let skip = rng.gen_range(0..count as usize);

		// this is tricky: the account might be our reward agent, which we never want to be
		// randomly chosen here. Try another one, or, if it is only our agent, return a random
		// one nonetheless.
		let candidate = PoolMembers::<T>::iter_keys().skip(skip).take(1).next().unwrap();
		let acc =
			if candidate == REWARD_AGENT_ACCOUNT { rng.gen::<AccountId>() } else { candidate };

		(RuntimeOrigin::signed(acc), acc)
	} else {
		// create a new account
		let acc = rng.gen::<AccountId>();
		(RuntimeOrigin::signed(acc), acc)
	}
}

fn random_ed_multiple<R: Rng>(rng: &mut R) -> Balance {
	let multiple = rng.gen_range(MIN_ED_MULTIPLE..MAX_ED_MULTIPLE);
	ExistentialDeposit::get() * multiple
}

fn fund_account<R: Rng>(rng: &mut R, account: &AccountId) {
	let target_amount = random_ed_multiple(rng);
	if let Some(top_up) = target_amount.checked_sub(Balances::free_balance(account)) {
		let _ = Balances::deposit_creating(account, top_up);
	}
	assert!(Balances::free_balance(account) >= target_amount);
}

fn random_existing_pool<R: Rng>(mut rng: &mut R) -> Option<PoolId> {
	BondedPools::<T>::iter_keys().collect::<Vec<_>>().choose(&mut rng).map(|x| *x)
}

fn random_call<R: Rng>(mut rng: &mut R) -> (pools::Call<T>, RuntimeOrigin) {
	let op = rng.gen::<usize>();
	let mut op_count = <pools::Call<T> as GetCallName>::get_call_names().len();
	// Exclude set_state, set_metadata, set_configs, update_roles and chill.
	op_count -= 5;

	match op % op_count {
		0 => {
			// join
			let pool_id = random_existing_pool(&mut rng).unwrap_or_default();
			let (origin, who) = random_signed_origin(&mut rng);
			fund_account(&mut rng, &who);
			let amount = random_ed_multiple(&mut rng);
			(PoolsCall::<T>::join { amount, pool_id }, origin)
		},
		1 => {
			// bond_extra
			let (origin, who) = random_signed_origin(&mut rng);
			let extra = if rng.gen::<bool>() {
				BondExtra::Rewards
			} else {
				fund_account(&mut rng, &who);
				let amount = random_ed_multiple(&mut rng);
				BondExtra::FreeBalance(amount)
			};
			(PoolsCall::<T>::bond_extra { extra }, origin)
		},
		2 => {
			// claim_payout
			let (origin, _) = random_signed_origin(&mut rng);
			(PoolsCall::<T>::claim_payout {}, origin)
		},
		3 => {
			// unbond
			let (origin, who) = random_signed_origin(&mut rng);
			let amount = random_ed_multiple(&mut rng);
			(PoolsCall::<T>::unbond { member_account: who, unbonding_points: amount }, origin)
		},
		4 => {
			// pool_withdraw_unbonded
			let pool_id = random_existing_pool(&mut rng).unwrap_or_default();
			let (origin, _) = random_signed_origin(&mut rng);
			(PoolsCall::<T>::pool_withdraw_unbonded { pool_id, num_slashing_spans: 0 }, origin)
		},
		5 => {
			// withdraw_unbonded
			let (origin, who) = random_signed_origin(&mut rng);
			(
				PoolsCall::<T>::withdraw_unbonded { member_account: who, num_slashing_spans: 0 },
				origin,
			)
		},
		6 => {
			// create
			let (origin, who) = random_signed_origin(&mut rng);
			let amount = random_ed_multiple(&mut rng);
			fund_account(&mut rng, &who);
			let root = who;
			let bouncer = who;
			let nominator = who;
			(PoolsCall::<T>::create { amount, root, bouncer, nominator }, origin)
		},
		7 => {
			// nominate
			let (origin, _) = random_signed_origin(&mut rng);
			let pool_id = random_existing_pool(&mut rng).unwrap_or_default();
			let validators = Default::default();
			(PoolsCall::<T>::nominate { pool_id, validators }, origin)
		},
		_ => unreachable!(),
	}
}

#[derive(Default)]
struct RewardAgent {
	who: AccountId,
	pool_id: Option<PoolId>,
	expected_reward: Balance,
}

// TODO: inject some slashes into the game.
impl RewardAgent {
	fn new(who: AccountId) -> Self {
		Self { who, ..Default::default() }
	}

	fn join(&mut self) {
		if self.pool_id.is_some() {
			return
		}
		let pool_id = LastPoolId::<T>::get();
		let amount = 10 * ExistentialDeposit::get();
		let origin = RuntimeOrigin::signed(self.who);
		let _ = Balances::deposit_creating(&self.who, 10 * amount);
		self.pool_id = Some(pool_id);
		log::info!(target: "reward-agent", "🤖 reward agent joining in {} with {}", pool_id, amount);
		assert_ok!(PoolsCall::join::<T> { amount, pool_id }.dispatch_bypass_filter(origin));
	}

	fn claim_payout(&mut self) {
		// 10 era later, we claim our payout. We expect our income to be roughly what we
		// calculated.
		if !PoolMembers::<T>::contains_key(&self.who) {
			log!(warn, "reward agent is not in the pool yet, cannot claim");
			return
		}
		let pre = Balances::free_balance(&42);
		let origin = RuntimeOrigin::signed(42);
		assert_ok!(PoolsCall::<T>::claim_payout {}.dispatch_bypass_filter(origin));
		let post = Balances::free_balance(&42);

		let income = post - pre;
		log::info!(
			target: "reward-agent", "🤖 CLAIM: actual: {}, expected: {}",
			income,
			self.expected_reward,
		);
		assert_eq_error_rate!(income, self.expected_reward, 10);
		self.expected_reward = 0;
	}
}

fn main() {
	let mut reward_agent = RewardAgent::new(REWARD_AGENT_ACCOUNT);
	sp_tracing::try_init_simple();
	let mut ext = sp_io::TestExternalities::new_empty();
	let mut events_histogram = Vec::<(PoolsEvents<T>, u32)>::default();
	let mut iteration = 0 as BlockNumber;
	let mut ok = 0;
	let mut err = 0;

	let dot: Balance = (10 as Balance).pow(10);
	ExistentialDeposit::set(dot);
	BondingDuration::set(8);

	ext.execute_with(|| {
		MaxPoolMembers::<T>::set(Some(10_000));
		MaxPoolMembersPerPool::<T>::set(Some(1000));
		MaxPools::<T>::set(Some(1_000));
		GlobalMaxCommission::<T>::set(Some(Perbill::from_percent(25)));

		MinCreateBond::<T>::set(10 * ExistentialDeposit::get());
		MinJoinBond::<T>::set(5 * ExistentialDeposit::get());
		System::set_block_number(1);
	});

	loop {
		fuzz!(|seed: [u8; 32]| {
			use ::rand::{rngs::SmallRng, SeedableRng};
			let mut rng = SmallRng::from_seed(seed);

			ext.execute_with(|| {
				let (call, origin) = random_call(&mut rng);
				let outcome = call.clone().dispatch_bypass_filter(origin.clone());
				iteration += 1;
				match outcome {
					Ok(_) => ok += 1,
					Err(_) => err += 1,
				};

				log!(
					trace,
					"iteration {}, call {:?}, origin {:?}, outcome: {:?}, so far {} ok {} err",
					iteration,
					call,
					origin,
					outcome,
					ok,
					err,
				);

				// possibly join the reward_agent
				if iteration > ERA / 2 && BondedPools::<T>::count() > 0 {
					reward_agent.join();
				}
				// and possibly roughly every 4 era, trigger payout for the agent. Doing this more
				// frequent is also harmless.
				if rng.gen_range(0..(4 * ERA)) == 0 {
					reward_agent.claim_payout();
				}

				// execute sanity checks at a fixed interval, possibly on every block.
				if iteration %
					(std::env::var("SANITY_CHECK_INTERVAL")
						.ok()
						.and_then(|x| x.parse::<u64>().ok()))
					.unwrap_or(1) == 0
				{
					log!(info, "running sanity checks at {}", iteration);
					Pools::do_try_state(u8::MAX).unwrap();
				}

				// collect and reset events.
				System::events()
					.into_iter()
					.map(|r| r.event)
					.filter_map(|e| {
						if let pallet_nomination_pools::mock::RuntimeEvent::Pools(inner) = e {
							Some(inner)
						} else {
							None
						}
					})
					.for_each(|e| {
						if let Some((_, c)) = events_histogram
							.iter_mut()
							.find(|(x, _)| std::mem::discriminant(x) == std::mem::discriminant(&e))
						{
							*c += 1;
						} else {
							events_histogram.push((e, 1))
						}
					});
				System::reset_events();

				// trigger an era change, and check the status of the reward agent.
				if iteration % ERA == 0 {
					CurrentEra::mutate(|c| *c += 1);
					BondedPools::<T>::iter().for_each(|(id, _)| {
						let amount = random_ed_multiple(&mut rng);
						let _ =
							Balances::deposit_creating(&Pools::create_reward_account(id), amount);
						// if we just paid out the reward agent, let's calculate how much we expect
						// our reward agent to have earned.
						if reward_agent.pool_id.map_or(false, |mid| mid == id) {
							let all_points = BondedPool::<T>::get(id).map(|p| p.points).unwrap();
							let member_points =
								PoolMembers::<T>::get(reward_agent.who).map(|m| m.points).unwrap();
							let agent_share = Perquintill::from_rational(member_points, all_points);
							log::info!(
								target: "reward-agent",
								"🤖 REWARD = amount = {:?}, ratio: {:?}, share {:?}",
								amount,
								agent_share,
								agent_share * amount,
							);
							reward_agent.expected_reward += agent_share * amount;
						}
					});

					log!(
						info,
						"iteration {}, {} pools, {} members, {} ok {} err, events = {:?}",
						iteration,
						BondedPools::<T>::count(),
						PoolMembers::<T>::count(),
						ok,
						err,
						events_histogram
							.iter()
							.map(|(x, c)| (
								format!("{:?}", x)
									.split(" ")
									.map(|x| x.to_string())
									.collect::<Vec<_>>()
									.first()
									.cloned()
									.unwrap(),
								c,
							))
							.collect::<Vec<_>>(),
					);
				}
			})
		})
	}
}
