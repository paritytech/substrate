// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run normalize`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug normalize hfuzz_workspace/normalize/*.fuzz`.

use honggfuzz::fuzz;
use sp_arithmetic::Normalizable;
use std::convert::TryInto;

fn main() {
	let sum_limit = u32::max_value() as u128;
	let len_limit: usize = u32::max_value().try_into().unwrap();

	loop {
		fuzz!(|data: (Vec<u32>, u32)| {
			let (data, norm) = data;
			if data.len() == 0 { return; }
			let pre_sum: u128 = data.iter().map(|x| *x as u128).sum();

			let normalized = data.normalize(norm);
			// error cases.
			if pre_sum > sum_limit || data.len() > len_limit {
				assert!(normalized.is_err())
			} else {
				if let Ok(normalized) = normalized {
					// if sum goes beyond u128, panic.
					let sum: u128 = normalized.iter().map(|x| *x as u128).sum();

					// if this function returns Ok(), then it will ALWAYS be accurate.
					assert_eq!(
						sum,
						norm as u128,
						"sums don't match {:?}, {}",
						normalized,
						norm,
					);
				}
			}
		})
	}
}
