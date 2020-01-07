// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Test utils

/// Panic when the vectors are different, without taking the order into account.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// # use substrate_test_utils::{assert_eq_uvec};
/// # fn main() {
/// assert_eq_uvec!(vec![1,2], vec![2,1]);
/// # }
/// ```
///
/// ```rust,should_panic
/// #[macro_use]
/// # use substrate_test_utils::{assert_eq_uvec};
/// # fn main() {
/// assert_eq_uvec!(vec![1,2,3], vec![2,1]);
/// # }
/// ```
#[macro_export]
macro_rules! assert_eq_uvec {
	( $x:expr, $y:expr ) => {
		$crate::__assert_eq_uvec!($x, $y);
		$crate::__assert_eq_uvec!($y, $x);
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __assert_eq_uvec {
	( $x:expr, $y:expr ) => {
		$x.iter().for_each(|e| {
			if !$y.contains(e) { panic!(format!("vectors not equal: {:?} != {:?}", $x, $y)); }
		});
	}
}
