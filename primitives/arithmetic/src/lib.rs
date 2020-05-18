// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Minimal fixed point arithmetic primitives and types for runtime.

#![cfg_attr(not(feature = "std"), no_std)]

/// Copied from `sp-runtime` and documented there.
#[macro_export]
macro_rules! assert_eq_error_rate {
	($x:expr, $y:expr, $error:expr $(,)?) => {
		assert!(
			($x) >= (($y) - ($error)) && ($x) <= (($y) + ($error)),
			"{:?} != {:?} (with error rate {:?})",
			$x,
			$y,
			$error,
		);
	};
}

pub mod biguint;
pub mod helpers_128bit;
pub mod traits;
mod per_things;
mod fixed64;
mod fixed128;
mod rational128;

pub use fixed64::Fixed64;
pub use fixed128::Fixed128;
pub use per_things::{PerThing, Percent, PerU16, Permill, Perbill, Perquintill};
pub use rational128::Rational128;

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn peru16_rational_does_not_overflow() {
		// A historical example that will panic only for per_thing type that are created with
		// maximum capacity of their type, e.g. PerU16.
		let _ = PerU16::from_rational_approximation(17424870u32, 17424870);
	}
}
