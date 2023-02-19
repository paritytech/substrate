// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Structs and helpers for distributing a voter's stake among various winners.

use crate::{ExtendedBalance, IdentifierT, PerThing128};
#[cfg(feature = "std")]
use codec::{Decode, Encode};
use sp_arithmetic::{
	traits::{Bounded, Zero},
	Normalizable, PerThing,
};
use sp_core::RuntimeDebug;
use sp_std::vec::Vec;

/// A voter's stake assignment among a set of targets, represented as ratios.
#[derive(RuntimeDebug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct Assignment<AccountId, P: PerThing> {
	/// Voter's identifier.
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, P)>,
}

impl<AccountId: IdentifierT, P: PerThing128> Assignment<AccountId, P> {
	/// Convert from a ratio assignment into one with absolute values aka. [`StakedAssignment`].
	///
	/// It needs `stake` which is the total budget of the voter.
	///
	/// Note that this might create _un-normalized_ assignments, due to accuracy loss of `P`. Call
	/// site might compensate by calling `try_normalize()` on the returned `StakedAssignment` as a
	/// post-precessing.
	///
	/// If an edge ratio is [`Bounded::min_value()`], it is dropped. This edge can never mean
	/// anything useful.
	pub fn into_staked(self, stake: ExtendedBalance) -> StakedAssignment<AccountId> {
		let distribution = self
			.distribution
			.into_iter()
			.filter_map(|(target, p)| {
				// if this ratio is zero, then skip it.
				if p.is_zero() {
					None
				} else {
					// NOTE: this mul impl will always round to the nearest number, so we might both
					// overflow and underflow.
					let distribution_stake = p * stake;
					Some((target, distribution_stake))
				}
			})
			.collect::<Vec<(AccountId, ExtendedBalance)>>();

		StakedAssignment { who: self.who, distribution }
	}

	/// Try and normalize this assignment.
	///
	/// If `Ok(())` is returned, then the assignment MUST have been successfully normalized to 100%.
	///
	/// ### Errors
	///
	/// This will return only if the internal `normalize` fails. This can happen if sum of
	/// `self.distribution.map(|p| p.deconstruct())` fails to fit inside `UpperOf<P>`. A user of
	/// this crate may statically assert that this can never happen and safely `expect` this to
	/// return `Ok`.
	pub fn try_normalize(&mut self) -> Result<(), &'static str> {
		self.distribution
			.iter()
			.map(|(_, p)| *p)
			.collect::<Vec<_>>()
			.normalize(P::one())
			.map(|normalized_ratios| {
				self.distribution.iter_mut().zip(normalized_ratios).for_each(
					|((_, old), corrected)| {
						*old = corrected;
					},
				)
			})
	}
}

/// A voter's stake assignment among a set of targets, represented as absolute values in the scale
/// of [`ExtendedBalance`].
#[derive(RuntimeDebug, Clone, Default)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Encode, Decode))]
pub struct StakedAssignment<AccountId> {
	/// Voter's identifier
	pub who: AccountId,
	/// The distribution of the voter's stake.
	pub distribution: Vec<(AccountId, ExtendedBalance)>,
}

impl<AccountId> StakedAssignment<AccountId> {
	/// Converts self into the normal [`Assignment`] type.
	///
	/// NOTE: This will always round down, and thus the results might be less than a full 100% `P`.
	/// Use a normalization post-processing to fix this. The data type returned here will
	/// potentially get used to create a compact type; a compact type requires sum of ratios to be
	/// less than 100% upon un-compacting.
	///
	/// If an edge stake is so small that it cannot be represented in `T`, it is ignored. This edge
	/// can never be re-created and does not mean anything useful anymore.
	pub fn into_assignment<P: PerThing>(self) -> Assignment<AccountId, P>
	where
		AccountId: IdentifierT,
	{
		let stake = self.total();
		// most likely, the size of the staked assignment and normal assignments will be the same,
		// so we pre-allocate it to prevent a sudden 2x allocation. `filter_map` starts with a size
		// of 0 by default.
		// https://www.reddit.com/r/rust/comments/3spfh1/does_collect_allocate_more_than_once_while/
		let mut distribution = Vec::<(AccountId, P)>::with_capacity(self.distribution.len());
		self.distribution.into_iter().for_each(|(target, w)| {
			let per_thing = P::from_rational(w, stake);
			if per_thing != Bounded::min_value() {
				distribution.push((target, per_thing));
			}
		});

		Assignment { who: self.who, distribution }
	}

	/// Try and normalize this assignment.
	///
	/// If `Ok(())` is returned, then the assignment MUST have been successfully normalized to
	/// `stake`.
	///
	/// NOTE: current implementation of `.normalize` is almost safe to `expect()` upon. The only
	/// error case is when the input cannot fit in `T`, or the sum of input cannot fit in `T`.
	/// Sadly, both of these are dependent upon the implementation of `VoteLimit`, i.e. the limit of
	/// edges per voter which is enforced from upstream. Hence, at this crate, we prefer returning a
	/// result and a use the name prefix `try_`.
	pub fn try_normalize(&mut self, stake: ExtendedBalance) -> Result<(), &'static str> {
		self.distribution
			.iter()
			.map(|(_, ref weight)| *weight)
			.collect::<Vec<_>>()
			.normalize(stake)
			.map(|normalized_weights| {
				self.distribution.iter_mut().zip(normalized_weights.into_iter()).for_each(
					|((_, weight), corrected)| {
						*weight = corrected;
					},
				)
			})
	}

	/// Get the total stake of this assignment (aka voter budget).
	pub fn total(&self) -> ExtendedBalance {
		self.distribution.iter().fold(Zero::zero(), |a, b| a.saturating_add(b.1))
	}
}
