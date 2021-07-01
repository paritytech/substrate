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

//! Proc macros to generate voter bag thresholds and associated items.

/// Calculate an appropriate constant ratio between thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn make_ratio(n: usize, bounds: impl std::ops::RangeBounds<VoteWeight>) -> f64;
/// ```
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::make_ratio;
/// /// Constant ratio between bag items. Approx. `1.248`.
/// const CONSTANT_RATIO: f64 = make_ratio!(200, ..);
/// ```
#[proc_macro]
pub fn make_ratio(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	todo!()
}

/// Make a constant array of threshold values suitable for use as voter bag thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn make_thresholds(n: usize, bounds: impl std::ops::RangeBounds<VoteWeight>) -> [VoteWeight; n];
/// ```
///
/// The output has these properties:
///
/// - Its length is `n`.
/// - Its first item respects `bounds.start_bound()`.
/// - Its last item respects `bounds.end_bound()`.
/// - There exists a constant ratio (see [`make_ratio`]) called _ratio_.
///
///   For all _k_, `output[k + 1] == (output[k] * ratio).round().min(output[k] + 1)`.
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::make_thresholds;
/// const THRESHOLDS: &[u64] = &make_thresholds!(200, ..);
/// ```
#[proc_macro]
pub fn make_thresholds(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	todo!()
}

/// Make a constant array of threshold values suitable for use as voter bag thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn edit_thresholds<const Old: usize, const New: usize>(
/// 	thresholds: [VoteWeight; Old],
/// 	inserting: impl IntoIterator<Item = VoteWeight>,
/// 	removing: impl IntoIterator<Item = VoteWeight>,
/// ) -> [VoteWeight; New];
/// ```
///
/// It is intended to be used to simply edit a thresholds list, inserting some items and removing
/// others, without needing to express the entire list.
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::{edit_thresholds, make_thresholds};
/// const THRESHOLDS: &[u64] = &edit_thresholds!(make_thresholds!(200, ..), [12345, 54321], []);
/// ```
#[proc_macro]
pub fn edit_thresholds(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	todo!()
}
