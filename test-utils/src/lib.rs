// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
	( $x:expr, $y:expr $(,)? ) => {
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
