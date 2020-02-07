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
#[cfg(test)]
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
mod rational128;

pub use fixed64::Fixed64;
pub use per_things::{Percent, Permill, Perbill, Perquintill};
pub use rational128::Rational128;
