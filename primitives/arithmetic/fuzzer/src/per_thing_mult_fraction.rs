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
//! Running this fuzzer can be done with `cargo hfuzz run per_thing_mult_fraction`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug per_thing_mult_fraction hfuzz_workspace/per_thing_mult_fraction/*.fuzz`.

use honggfuzz::fuzz;
use sp_arithmetic::{PerThing, Perbill, Percent, Perquintill, *};

/// Tries to disprove `(n / d) * d <= n` for any `PerThing`s.
fn main() {
	loop {
		fuzz!(|data: (u128, u128)| {
			let (n, d) = (data.0.min(data.1), data.0.max(data.1).max(1));

			check_mul::<PerU16>(n, d);
			check_mul::<Percent>(n, d);
			check_mul::<Perbill>(n, d);
			check_mul::<Perquintill>(n, d);

			check_reciprocal_mul::<PerU16>(n, d);
			check_reciprocal_mul::<Percent>(n, d);
			check_reciprocal_mul::<Perbill>(n, d);
			check_reciprocal_mul::<Perquintill>(n, d);
		})
	}
}

/// Checks that `(n / d) * d <= n`.
fn check_mul<P: PerThing>(n: u128, d: u128)
where
	P: PerThing + core::ops::Mul<u128, Output = u128>,
{
	let q = P::from_rational_with_rounding(n, d, Rounding::Down).unwrap();
	assert!(q * d <= n, "{:?} * {:?} <= {:?}", q, d, n);
}

/// Checks that `n / (n / d) >= d`.
fn check_reciprocal_mul<P: PerThing>(n: u128, d: u128)
where
	P: PerThing + core::ops::Mul<u128, Output = u128>,
{
	let q = P::from_rational_with_rounding(n, d, Rounding::Down).unwrap();
	if q.is_zero() {
		return
	}

	let r = q.saturating_reciprocal_mul_floor(n);
	assert!(r >= d, "{} / ({} / {}) != {} but {}", n, n, d, d, r);
}
