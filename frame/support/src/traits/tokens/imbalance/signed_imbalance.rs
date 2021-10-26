// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Convenience type for managing an imbalance whose sign is unknown.

use super::super::imbalance::Imbalance;
use crate::traits::misc::SameOrOther;
use codec::FullCodec;
use sp_runtime::traits::{AtLeast32BitUnsigned, MaybeSerializeDeserialize};
use sp_std::fmt::Debug;

/// Either a positive or a negative imbalance.
pub enum SignedImbalance<B, PositiveImbalance: Imbalance<B>> {
	/// A positive imbalance (funds have been created but none destroyed).
	Positive(PositiveImbalance),
	/// A negative imbalance (funds have been destroyed but none created).
	Negative(PositiveImbalance::Opposite),
}

impl<
		P: Imbalance<B, Opposite = N>,
		N: Imbalance<B, Opposite = P>,
		B: AtLeast32BitUnsigned + FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default,
	> SignedImbalance<B, P>
{
	/// Create a `Positive` instance of `Self` whose value is zero.
	pub fn zero() -> Self {
		SignedImbalance::Positive(P::zero())
	}

	/// Drop `Self` if and only if it is equal to zero. Return `Err` with `Self` if not.
	pub fn drop_zero(self) -> Result<(), Self> {
		match self {
			SignedImbalance::Positive(x) => x.drop_zero().map_err(SignedImbalance::Positive),
			SignedImbalance::Negative(x) => x.drop_zero().map_err(SignedImbalance::Negative),
		}
	}

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	pub fn merge(self, other: Self) -> Self {
		match (self, other) {
			(SignedImbalance::Positive(one), SignedImbalance::Positive(other)) =>
				SignedImbalance::Positive(one.merge(other)),
			(SignedImbalance::Negative(one), SignedImbalance::Negative(other)) =>
				SignedImbalance::Negative(one.merge(other)),
			(SignedImbalance::Positive(one), SignedImbalance::Negative(other)) => {
				match one.offset(other) {
					SameOrOther::Same(positive) => SignedImbalance::Positive(positive),
					SameOrOther::Other(negative) => SignedImbalance::Negative(negative),
					SameOrOther::None => SignedImbalance::Positive(P::zero()),
				}
			},
			(one, other) => other.merge(one),
		}
	}
}
