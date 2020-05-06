// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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
