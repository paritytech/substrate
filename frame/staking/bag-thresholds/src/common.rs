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

//! Features common between the other modules of this crate.

use syn::{Expr, Result, Token, Type, parse::{Parse, ParseStream}};

/// Parse function-like input parameters
///
/// ```ignore
/// fn my_fn(n: usize, VoteWeight: Type, existential_weight: VoteWeight);
/// ```
///
/// - The argument `n` is how many divisions we're partitioning `VoteWeight` into. It may be any
///   expression which is evaluable in a const context.
/// - `VoteWeight` is the type of the vote weight, and should typically be a typedef. It must have a
///   `::MAX` attribute available.
/// - `existential_weight` is the weight below which it's not worth examining a voter. Typically,
///   this will be the result of some calculation involving the existential deposit for a chain's
///   balance type. It may be any expression which is evaluable in a const context.
pub struct ThresholdParams {
	pub n: Expr,
	pub comma1: Token![,],
	pub vote_weight: Type,
	pub comma2: Token![,],
	pub existential_weight: Expr,
	pub comma3: Option<Token![,]>,
}

impl Parse for ThresholdParams {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
			n: input.parse()?,
			comma1: input.parse()?,
			vote_weight: input.parse()?,
			comma2: input.parse()?,
			existential_weight: input.parse()?,
			comma3: input.parse()?,
		})
    }
}
