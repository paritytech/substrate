// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Utilities for remote-testing pallet-bags-list.

use sp_std::prelude::*;

/// A common log target to use.
pub const LOG_TARGET: &'static str = "runtime::bags-list::remote-tests";

pub mod migration;
pub mod sanity_check;
pub mod snapshot;

/// A wrapper for a runtime that the functions of this crate expect.
///
/// For example, this can be the `Runtime` type of the Polkadot runtime.
pub trait RuntimeT:
	pallet_staking::Config + pallet_bags_list::Config + frame_system::Config
{
}
impl<T: pallet_staking::Config + pallet_bags_list::Config + frame_system::Config> RuntimeT for T {}

fn percent(portion: u32, total: u32) -> f64 {
	(portion as f64 / total as f64) * 100f64
}

/// Display the number of nodes in each bag, while identifying those that need a rebag.
pub fn display_and_check_bags<Runtime: RuntimeT>(currency_unit: u64, currency_name: &'static str) {
	use frame_election_provider_support::SortedListProvider;
	use frame_support::traits::Get;

	let min_nominator_bond = <pallet_staking::MinNominatorBond<Runtime>>::get();
	log::info!(target: LOG_TARGET, "min nominator bond is {:?}", min_nominator_bond);

	let voter_list_count = <Runtime as pallet_staking::Config>::SortedListProvider::count();

	// go through every bag to track the total number of voters within bags and log some info about
	// how voters are distributed within the bags.
	let mut seen_in_bags = 0;
	let mut rebaggable = 0;
	let mut active_bags = 0;
	for vote_weight_thresh in <Runtime as pallet_bags_list::Config>::BagThresholds::get() {
		// threshold in terms of UNITS (e.g. KSM, DOT etc)
		let vote_weight_thresh_as_unit = *vote_weight_thresh as f64 / currency_unit as f64;
		let pretty_thresh = format!("Threshold: {}. {}", vote_weight_thresh_as_unit, currency_name);

		let bag = match pallet_bags_list::Pallet::<Runtime>::list_bags_get(*vote_weight_thresh) {
			Some(bag) => bag,
			None => {
				log::info!(target: LOG_TARGET, "{} NO VOTERS.", pretty_thresh);
				continue
			},
		};

		active_bags += 1;

		for id in bag.std_iter().map(|node| node.std_id().clone()) {
			let vote_weight = pallet_staking::Pallet::<Runtime>::weight_of(&id);
			let vote_weight_as_balance: pallet_staking::BalanceOf<Runtime> =
				vote_weight.try_into().map_err(|_| "can't convert").unwrap();

			if vote_weight_as_balance < min_nominator_bond {
				log::trace!(
					target: LOG_TARGET,
					"⚠️ {} Account found below min bond: {:?}.",
					pretty_thresh,
					id
				);
			}

			let node =
				pallet_bags_list::Node::<Runtime>::get(&id).expect("node in bag must exist.");
			if node.is_misplaced(vote_weight) {
				rebaggable += 1;
				log::trace!(
					target: LOG_TARGET,
					"Account {:?} can be rebagged from {:?} to {:?}",
					id,
					vote_weight_thresh_as_unit,
					pallet_bags_list::notional_bag_for::<Runtime>(vote_weight) as f64 /
						currency_unit as f64
				);
			}
		}

		// update our overall counter
		let voters_in_bag = bag.std_iter().count() as u32;
		seen_in_bags += voters_in_bag;

		// percentage of all nominators
		let percent_of_voters = percent(voters_in_bag, voter_list_count);

		log::info!(
			target: LOG_TARGET,
			"{} Nominators: {} [%{:.3}]",
			pretty_thresh,
			voters_in_bag,
			percent_of_voters,
		);
	}

	if seen_in_bags != voter_list_count {
		log::error!(
			target: LOG_TARGET,
			"bags list population ({}) not on par whoever is voter_list ({})",
			seen_in_bags,
			voter_list_count,
		)
	}

	log::info!(
		target: LOG_TARGET,
		"a total of {} nodes are in {} active bags [{} total bags], {} of which can be rebagged.",
		voter_list_count,
		active_bags,
		<Runtime as pallet_bags_list::Config>::BagThresholds::get().len(),
		rebaggable,
	);
}
