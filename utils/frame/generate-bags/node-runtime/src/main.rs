// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Make the set of bag thresholds to be used with pallet-bags-list.

use clap::Parser;
use generate_bags::generate_thresholds;
use std::path::PathBuf;

#[derive(Debug, Parser)]
// #[clap(author, version, about)]
struct Opt {
	/// How many bags to generate.
	#[clap(long, default_value = "200")]
	n_bags: usize,

	/// Where to write the output.
	output: PathBuf,

	/// The total issuance of the currency used to create `VoteWeight`.
	#[clap(short, long)]
	total_issuance: u128,

	/// The minimum account balance (i.e. existential deposit) for the currency used to create
	/// `VoteWeight`.
	#[clap(short, long)]
	minimum_balance: u128,
}

fn main() -> Result<(), std::io::Error> {
	let Opt { n_bags, output, total_issuance, minimum_balance } = Opt::parse();
	generate_thresholds::<node_runtime::Runtime>(n_bags, &output, total_issuance, minimum_balance)
}
