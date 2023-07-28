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

use fraction::prelude::BigFraction as Fraction;
use honggfuzz::fuzz;
use sp_arithmetic::{MultiplyRational, Rounding, Rounding::*};

/// Tries to demonstrate that `multiply_by_rational_with_rounding` is incorrect.
fn main() {
	loop {
		fuzz!(|data: (u128, u128, u128, ArbitraryRounding)| {
			let (f, n, d, r) = (data.0, data.1, data.2, data.3 .0);

			check::<u8>(f as u8, n as u8, d as u8, r);
			check::<u16>(f as u16, n as u16, d as u16, r);
			check::<u32>(f as u32, n as u32, d as u32, r);
			check::<u64>(f as u64, n as u64, d as u64, r);
			check::<u128>(f, n, d, r);
		})
	}
}

fn check<N>(f: N, n: N, d: N, r: Rounding)
where
	N: MultiplyRational + Into<u128> + Copy + core::fmt::Debug,
{
	let Some(got) = f.multiply_rational(n, d, r) else { return };

	let (ae, be, ce) =
		(Fraction::from(f.into()), Fraction::from(n.into()), Fraction::from(d.into()));
	let want = round(ae * be / ce, r);

	assert_eq!(
		Fraction::from(got.into()),
		want,
		"{:?} * {:?} / {:?} = {:?} != {:?}",
		f,
		n,
		d,
		got,
		want
	);
}

/// Round a `Fraction` according to the given mode.
fn round(f: Fraction, r: Rounding) -> Fraction {
	match r {
		Up => f.ceil(),
		NearestPrefUp =>
			if f.fract() < Fraction::from(0.5) {
				f.floor()
			} else {
				f.ceil()
			},
		Down => f.floor(),
		NearestPrefDown =>
			if f.fract() > Fraction::from(0.5) {
				f.ceil()
			} else {
				f.floor()
			},
	}
}

/// An [`arbitrary::Arbitrary`] [`Rounding`] mode.
struct ArbitraryRounding(Rounding);
impl arbitrary::Arbitrary<'_> for ArbitraryRounding {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		Ok(Self(match u.int_in_range(0..=3).unwrap() {
			0 => Up,
			1 => NearestPrefUp,
			2 => Down,
			3 => NearestPrefDown,
			_ => unreachable!(),
		}))
	}
}
