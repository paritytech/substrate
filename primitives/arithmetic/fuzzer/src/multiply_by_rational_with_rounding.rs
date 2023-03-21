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
//! Running this fuzzer can be done with `cargo hfuzz run multiply_by_rational_with_rounding`.
//! `honggfuzz` CLI options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4
//! threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug multiply_by_rational_with_rounding
//! hfuzz_workspace/multiply_by_rational_with_rounding/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use honggfuzz::fuzz;
use primitive_types::U256;
use sp_arithmetic::{
	helpers_128bit::multiply_by_rational_with_rounding, traits::SaturatedConversion, Rounding,
};

/// Tries to demonstrate that `multiply_by_rational_with_rounding` is incorrect.
fn main() {
	loop {
		fuzz!(|data: (u128, u128, u128)| {
			let (a, b, c) = (data.0.max(1), data.1, data.2.max(1));
			let Some(got) = multiply_by_rational_with_rounding(a, b, c, Rounding::Down) else {
				return;
			};

			let (a, b, c) = (U256::from(a), U256::from(b), U256::from(c));
			let want = (a * b / c).saturated_into();

			assert_eq!(got, want, "{:?} * {:?} / {:?} = {:?} != {:?}", a, b, c, got, want);
		})
	}
}
