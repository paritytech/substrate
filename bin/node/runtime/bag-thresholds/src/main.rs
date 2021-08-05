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

//! Make the set of bag thresholds to be used in pallet-bags-list.

use pallet_bags_list::make_bags::generate_thresholds_module;
use std::path::PathBuf;
use structopt::StructOpt;
use node_runtime::Runtime;
use frame_support::traits::{Currency, CurrencyToVote};

#[derive(Debug, StructOpt)]
struct Opt {
	/// How many bags to generate.
	#[structopt(long, default_value = "200")]
	n_bags: usize,

	/// Where to write the output.
	output: PathBuf,
}

fn main() -> Result<(), std::io::Error> {
	let Opt { n_bags, output } = Opt::from_args();
	let mut ext = sp_io::TestExternalities::new_empty();



	let res = ext.execute_with(||{
		// let existential_deposit = <Runtime::Currency as Currency<Runtime::AccountId>>::minimum_balance();
		let existential_deposit = <Runtime as pallet_staking::Config>::Currency::minimum_balance();
		let issuance = <Runtime as pallet_staking::Config>::Currency::total_issuance();
		let existential_weight = <Runtime as pallet_staking::Config>::CurrencyToVote::to_vote(existential_deposit, issuance);

		generate_thresholds_module::<node_runtime::Runtime>(n_bags, existential_weight, &output);
	});

	Ok(res)
}
