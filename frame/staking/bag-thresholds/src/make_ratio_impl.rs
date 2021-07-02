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

//! Implementation for the `make_ratio` proc macro.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, parse_quote};

use crate::common::ThresholdParams;

/// Calculate an appropriate constant ratio between thresholds.
///
/// This macro can be thought of as a function with signature
///
/// ```ignore
/// pub const fn make_ratio(n: usize, VoteWeight: Type, existential_weight: VoteWeight) -> f64;
/// ```
///
/// # Calculation
///
/// The constant ratio is calculated per `exp(ln(VoteWeight::MAX - existential_weight) / n).
pub fn make_ratio(input: TokenStream) -> TokenStream {
	let ThresholdParams{
		n,
		vote_weight,
		existential_weight,
		..
	} = parse_macro_input!(input as ThresholdParams);

	let n = parse_quote!(#n) as f64;
	let diff_weight = parse_quote!(#vote_weight::MAX - #existential_weight) as f64;

	let ratio = (diff_weight.ln() / n).exp();

	quote!(#ratio).into()
}
