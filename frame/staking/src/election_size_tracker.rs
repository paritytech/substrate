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

//! ## A static size tracker for the election snapshot data.
//!
//! ### Overview
//!
//! The goal of the size tracker is to provide a static, no-allocation byte tracker to be
//! used by the election data provider when preparing the results of
//! [`ElectionDataProvider::electing_voters`]. The [`StaticTracker`] implementation uses
//! [`codec::Encode::size_hint`] to estimate the SCALE encoded size of the snapshot voters struct
//! as it is being constructed without requiring extra stack allocations.
//!
//! The [`StaticTracker::try_register_voter`] is called to update the static tracker internal
//! state, if It will return an error if the resulting SCALE encoded size (in bytes) is larger than
//! the provided `DataProviderBounds`.
//!
//! ### Example
//!
//! ```ignore
//! use pallet_staking::election_size_tracker::*;
//!
//! // instantiates a new tracker.
//! let mut size_tracker = StaticTracker::<Staking>::default();
//!
//! let voter_bounds = ElectionBoundsBuilder::default().voter_size(1_00.into()).build().voters;
//!
//! let mut sorted_voters = T::VoterList.iter();
//! let mut selected_voters = vec![];
//!
//! // fit as many voters in the vec as the bounds permit.
//! for v in sorted_voters {
//!     let voter = (v, weight_of(&v), targets_of(&v));
//!     if size_tracker.try_register_voter(&voter, &voter_bounds).is_err() {
//!         // voter bounds size exhausted
//!         break;
//!     }
//!     selected_voters.push(voter);
//! }
//!
//! // The SCALE encoded size in bytes of `selected_voters` is guaranteed to be below
//! // `voter_bounds`.
//! debug_assert!(
//!     selected_voters.encoded_size() <=
//!     SizeTracker::<Staking>::final_byte_size_of(size_tracker.num_voters, size_tracker.size)
//! );
//! ```
//!
//! ### Implementation Details
//!
//! The current implementation of the static tracker is tightly coupled with the staking pallet
//! implementation, namely the representation of a voter ([`VoterOf`]). The SCALE encoded byte size
//! is calculated using [`Encode::size_hint`] of each type in the voter tuple. Each voter's byte
//! size is the sum of:
//! - 1 * [`Encode::size_hint`] of the `AccountId` type;
//! - 1 * [`Encode::size_hint`] of the `VoteWeight` type;
//! - `num_votes` * [`Encode::size_hint`] of the `AccountId` type.

use codec::Encode;
use frame_election_provider_support::{
	bounds::{DataProviderBounds, SizeBound},
	ElectionDataProvider, VoterOf,
};

/// Keeps track of the SCALE encoded byte length of the snapshot's voters or targets.
///
/// The tracker calculates the bytes used based on static rules, without requiring any actual
/// encoding or extra allocations.
#[derive(Clone, Copy, Debug)]
pub struct StaticTracker<DataProvider> {
	pub size: usize,
	pub counter: usize,
	_marker: sp_std::marker::PhantomData<DataProvider>,
}

impl<DataProvider> Default for StaticTracker<DataProvider> {
	fn default() -> Self {
		Self { size: 0, counter: 0, _marker: Default::default() }
	}
}

impl<DataProvider> StaticTracker<DataProvider>
where
	DataProvider: ElectionDataProvider,
{
	/// Tries to register a new voter.
	///
	/// If the new voter exhausts the provided bounds, return an error. Otherwise, the internal
	/// state of the tracker is updated with the new registered voter.
	pub fn try_register_voter(
		&mut self,
		voter: &VoterOf<DataProvider>,
		bounds: &DataProviderBounds,
	) -> Result<(), ()> {
		let tracker_size_after = {
			let voter_hint = Self::voter_size_hint(voter);
			Self::final_byte_size_of(self.counter + 1, self.size.saturating_add(voter_hint))
		};

		match bounds.size_exhausted(SizeBound(tracker_size_after as u32)) {
			true => Err(()),
			false => {
				self.size = tracker_size_after;
				self.counter += 1;
				Ok(())
			},
		}
	}

	/// Calculates the size of the voter to register based on [`Encode::size_hint`].
	fn voter_size_hint(voter: &VoterOf<DataProvider>) -> usize {
		let (voter_account, vote_weight, targets) = voter;

		voter_account
			.size_hint()
			.saturating_add(vote_weight.size_hint())
			.saturating_add(voter_account.size_hint().saturating_mul(targets.len()))
	}

	/// Tries to register a new target.
	///
	/// If the new target exhausts the provided bounds, return an error. Otherwise, the internal
	/// state of the tracker is updated with the new registered target.
	pub fn try_register_target(
		&mut self,
		target: DataProvider::AccountId,
		bounds: &DataProviderBounds,
	) -> Result<(), ()> {
		let tracker_size_after = Self::final_byte_size_of(
			self.counter + 1,
			self.size.saturating_add(target.size_hint()),
		);

		match bounds.size_exhausted(SizeBound(tracker_size_after as u32)) {
			true => Err(()),
			false => {
				self.size = tracker_size_after;
				self.counter += 1;
				Ok(())
			},
		}
	}

	/// Size of the SCALE encoded prefix with a given length.
	#[inline]
	fn length_prefix(len: usize) -> usize {
		use codec::{Compact, CompactLen};
		Compact::<u32>::compact_len(&(len as u32))
	}

	/// Calculates the final size in bytes of the SCALE encoded snapshot voter struct.
	fn final_byte_size_of(num_voters: usize, size: usize) -> usize {
		Self::length_prefix(num_voters).saturating_add(size)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		mock::{AccountId, Staking, Test},
		BoundedVec, MaxNominationsOf,
	};
	use frame_election_provider_support::bounds::ElectionBoundsBuilder;
	use sp_core::bounded_vec;

	type Voters = BoundedVec<AccountId, MaxNominationsOf<Test>>;

	#[test]
	pub fn election_size_tracker_works() {
		let mut voters: Vec<(u64, u64, Voters)> = vec![];
		let mut size_tracker = StaticTracker::<Staking>::default();
		let voter_bounds = ElectionBoundsBuilder::default().voters_size(1_50.into()).build().voters;

		// register 1 voter with 1 vote.
		let voter = (1, 10, bounded_vec![2]);
		assert!(size_tracker.try_register_voter(&voter, &voter_bounds).is_ok());
		voters.push(voter);

		assert_eq!(
			StaticTracker::<Staking>::final_byte_size_of(size_tracker.counter, size_tracker.size),
			voters.encoded_size()
		);

		// register another voter, now with 3 votes.
		let voter = (2, 20, bounded_vec![3, 4, 5]);
		assert!(size_tracker.try_register_voter(&voter, &voter_bounds).is_ok());
		voters.push(voter);

		assert_eq!(
			StaticTracker::<Staking>::final_byte_size_of(size_tracker.counter, size_tracker.size),
			voters.encoded_size()
		);

		// register noop vote (unlikely to happen).
		let voter = (3, 30, bounded_vec![]);
		assert!(size_tracker.try_register_voter(&voter, &voter_bounds).is_ok());
		voters.push(voter);

		assert_eq!(
			StaticTracker::<Staking>::final_byte_size_of(size_tracker.counter, size_tracker.size),
			voters.encoded_size()
		);
	}

	#[test]
	pub fn election_size_tracker_bounds_works() {
		let mut voters: Vec<(u64, u64, Voters)> = vec![];
		let mut size_tracker = StaticTracker::<Staking>::default();
		let voter_bounds = ElectionBoundsBuilder::default().voters_size(1_00.into()).build().voters;

		let voter = (1, 10, bounded_vec![2]);
		assert!(size_tracker.try_register_voter(&voter, &voter_bounds).is_ok());
		voters.push(voter);

		assert_eq!(
			StaticTracker::<Staking>::final_byte_size_of(size_tracker.counter, size_tracker.size),
			voters.encoded_size()
		);

		assert!(size_tracker.size > 0 && size_tracker.size < 1_00);
		let size_before_overflow = size_tracker.size;

		// try many voters that will overflow the tracker's buffer.
		let voter = (2, 10, bounded_vec![2, 3, 4, 5, 6, 7, 8, 9]);
		voters.push(voter.clone());

		assert!(size_tracker.try_register_voter(&voter, &voter_bounds).is_err());
		assert!(size_tracker.size > 0 && size_tracker.size < 1_00);

		// size of the tracker did not update when trying to register votes failed.
		assert_eq!(size_tracker.size, size_before_overflow);
	}

	#[test]
	fn len_prefix_works() {
		let length_samples =
			vec![0usize, 1, 62, 63, 64, 16383, 16384, 16385, 1073741822, 1073741823, 1073741824];

		for s in length_samples {
			// the encoded size of a vector of n bytes should be n + the length prefix
			assert_eq!(vec![1u8; s].encoded_size(), StaticTracker::<Staking>::length_prefix(s) + s);
		}
	}
}
