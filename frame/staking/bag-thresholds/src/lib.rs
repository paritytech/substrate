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

use proc_macro::TokenStream;

mod common;
mod make_ratio_impl;

/// Calculate an appropriate constant ratio between thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn make_ratio(n: usize, VoteWeight: Type, existential_weight: VoteWeight) -> f64;
/// ```
///
/// - The argument `n` is how many divisions we're partitioning `VoteWeight` into. It may be any
///   expression which is evaluable in a const context.
/// - `VoteWeight` is the type of the vote weight, and should typically be a typedef. It must have a
///   `::MAX` attribute available.
/// - `existential_weight` is the weight below which it's not worth examining a voter. Typically,
///   this will be the result of some calculation involving the existential deposit for a chain's
///   balance type. It may be any expression which is evaluable in a const context.
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::make_ratio;
/// /// Constant ratio between bag items. Approx. `1.248`.
/// const CONSTANT_RATIO: f64 = make_ratio!(200, u64, 0);
/// ```
///
/// # Calculation
///
/// The constant ratio is calculated per `exp(ln(VoteWeight::MAX - existential_weight) / n).
#[proc_macro]
pub fn make_ratio(input: TokenStream) -> TokenStream {
	make_ratio_impl::make_ratio(input)
}

/// Make a constant array of threshold values suitable for use as voter bag thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn make_thresholds(n: usize, VoteWeight: Type, existential_weight: VoteWeight) -> [VoteWeight; n];
/// ```
///
/// - The argument `n` is how many divisions we're partitioning `VoteWeight` into. It may be any
///   expression which is evaluable in a const context.
/// - `VoteWeight` is the type of the vote weight, and should typically be a typedef. It must have a
///   `::MAX` attribute available.
/// - `existential_weight` is the weight below which it's not worth examining a voter. Typically,
///   this will be the result of some calculation involving the existential deposit for a chain's
///   balance type. It may be any expression which is evaluable in a const context.
///
/// The output has these properties:
///
/// - Its length is `n`.
/// - Its first item is greater than or equal to `existential_weight`.
/// - Its last item is equal to `VoteWeight::MAX`.
/// - There exists a constant ratio (see [`make_ratio`]) called _ratio_.
///
///   For all _k_ in `0..(n-1)`, `output[k + 1] == (output[k] * ratio).round()`.
///
/// However, there are two exceptions to the ratio rule:
///
/// - As thresholds may not duplicate, if `(output[k] * ratio).round() == output[k]`, then `output[k
///   + 1] == output[k] + 1`.
/// - Due to the previous exception in combination with the requirement that the final item is equal
///   to `VoteWeight::MAX`, the ratio of the final item may diverge from the common ratio.
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::make_thresholds;
/// const THRESHOLDS: [u64; 200] = &make_thresholds!(200, u64, 0);
/// ```
#[proc_macro]
pub fn make_thresholds(input: TokenStream) -> TokenStream {
	todo!()
}

/// Make a constant array of threshold values suitable for use as voter bag thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn edit_thresholds<
/// 	const Old: usize,
/// 	const Inserting: usize,
/// 	const Removing: usize,
/// 	const New: usize,
/// >(
/// 	thresholds: [VoteWeight; Old],
/// 	inserting: [VoteWeight; Inserting],
/// 	removing: [VoteWeight; Removing],
/// ) -> [VoteWeight; New];
/// ```
///
/// It is intended to be used to simply edit a thresholds list, inserting some items and removing
/// others, without needing to express the entire list.
///
/// Note that due to macro limitations, `inserting` and `removing` must be array literals.
///
/// Note that `removing` overrides `inserting`: if a value appears in both lists, it does not appear
/// in the output.
///
/// # Example:
///
/// ```
/// # use pallet_staking_voter_bag_thresholds::{edit_thresholds, make_thresholds};
/// const THRESHOLDS: &[u64] = &edit_thresholds!(make_thresholds!(200, u64, 0), [12345, 54321], []);
/// ```
#[proc_macro]
pub fn edit_thresholds(input: TokenStream) -> TokenStream {
	todo!()
}
