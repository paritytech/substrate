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

//! Make the set of voting bag thresholds to be used in `voter_bags.rs`.

const N_BAGS: usize = 200;

fn main() {
	let ratio = ((u64::MAX as f64).ln() / (N_BAGS as f64)).exp();
	println!("pub const CONSTANT_RATIO: f64 = {};", ratio);

	let mut thresholds = Vec::with_capacity(N_BAGS as usize);

	while thresholds.len() < N_BAGS as usize {
		let prev_item: u64 = thresholds.last().copied().unwrap_or_default();
		let item = (prev_item as f64 * ratio).round().max(prev_item as f64 + 1.0);
		thresholds.push(item as u64);
	}

	*thresholds.last_mut().unwrap() = u64::MAX;

	println!("pub const THRESHOLDS: [u64; {}] = {:#?};", N_BAGS, thresholds);

	debug_assert_eq!(thresholds.len(), N_BAGS as usize);
	debug_assert_eq!(*thresholds.last().unwrap(), u64::MAX);
}
