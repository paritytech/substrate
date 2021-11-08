// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Miscellaneous additional datatypes.

use super::*;
use codec::{Decode, Encode};
use frame_support::Parameter;
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
pub type CallOf<T> = <T as Config>::Call;
pub type OriginOf<T> = <T as Config>::Origin;
pub type VotesOf<T> = <T as Config>::Votes;
pub type TallyOf<T> = <T as Config>::Tally;
pub type ReferendumInfoOf<T> = ReferendumInfo<
	TrackIdOf<T>,
	OriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	VotesOf<T>,
	TallyOf<T>,
	<T as frame_system::Config>::AccountId,
>;
pub type ReferendumStatusOf<T> = ReferendumStatus<
	TrackIdOf<T>,
	OriginOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	VotesOf<T>,
	TallyOf<T>,
	<T as frame_system::Config>::AccountId,
>;
pub type DecidingStatusOf<T> = DecidingStatus<
	<T as frame_system::Config>::BlockNumber,
>;
pub type TrackInfoOf<T> = TrackInfo<
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;
pub type TrackIdOf<T> = <
	<T as Config>::Tracks as TracksInfo<
		BalanceOf<T>,
		<T as frame_system::Config>::BlockNumber,
	>
>::Id;

/// A referendum index.
pub type ReferendumIndex = u32;

pub trait InsertSorted<T> {
	/// Inserts an item into a sorted series.
	///
	/// Returns `true` if it was inserted, `false` if it would belong beyond the bound of the
	/// series.
	fn insert_sorted_by_key<
		F: FnMut(&T) -> K,
		K: PartialOrd<K> + Ord,
	>(&mut self, t: T, f: F,) -> bool;
}
impl<T: Ord, S: Get<u32>> InsertSorted<T> for BoundedVec<T, S> {
	fn insert_sorted_by_key<
		F: FnMut(&T) -> K,
		K: PartialOrd<K> + Ord,
	>(&mut self, t: T, mut f: F,) -> bool {
		let index = self.binary_search_by_key::<K, F>(&f(&t), f).unwrap_or_else(|x| x);
		if index >= S::get() as usize {
			return false
		}
		self.force_insert(index, t);
		true
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct DecidingStatus<BlockNumber> {
	/// When this referendum will end. If confirming, then the
	/// end will actually be delayed until the end of the confirmation period.
	pub(crate) ending: BlockNumber,
	/// How long we will be deciding on this referendum for.
	pub(crate) period: BlockNumber,
	/// If `Some`, then the referendum has entered confirmation stage and will end at
	/// the block number as long as it doesn't lose its approval in the meantime.
	pub(crate) confirming: Option<BlockNumber>,
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Deposit<AccountId, Balance> {
	pub(crate) who: AccountId,
	pub(crate) amount: Balance,
}

#[derive(Clone, Encode, TypeInfo)]
pub struct TrackInfo<Balance, Moment> {
	/// Name of this track.
	pub(crate) name: &'static str,
	/// A limit for the number of referenda on this track that can be being decided at once.
	/// For Root origin this should generally be just one.
	pub(crate) max_deciding: u32,
	/// Amount that must be placed on deposit before a decision can be made.
	pub(crate) decision_deposit: Balance,
	/// Amount of time this must be submitted for before a decision can be made.
	pub(crate) prepare_period: Moment,
	/// Amount of time that a decision may take to be approved prior to cancellation.
	pub(crate) decision_period: Moment,
	/// Amount of time that the approval criteria must hold before it can be approved.
	pub(crate) confirm_period: Moment,
	/// Minimum amount of time that an approved proposal must be in the dispatch queue.
	pub(crate) min_enactment_period: Moment,
	/// Minimum aye votes as percentage of overall conviction-weighted votes needed for
	/// approval as a function of time into decision period.
	pub(crate) min_approval: Curve,
	/// Minimum turnout as percentage of overall population that is needed for
	/// approval as a function of time into decision period.
	pub(crate) min_turnout: Curve,
}

pub trait TracksInfo<Balance, Moment> {
	type Id: Copy + Eq + Codec + TypeInfo + Parameter + Ord + PartialOrd;
	type Origin;
	fn tracks() -> &'static [(Self::Id, TrackInfo<Balance, Moment>)];
	fn track_for(id: &Self::Origin) -> Result<Self::Id, ()>;
}

/// Indication of either a specific moment or a delay from a implicitly defined moment.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum AtOrAfter<Moment> {
	/// Indiciates that the event should occur at the moment given.
	At(Moment),
	/// Indiciates that the event should occur some period of time (defined by the parameter) after
	/// a prior event. The prior event is defined by the context, but for the purposes of referendum
	/// proposals, the "prior event" is the passing of the referendum.
	After(Moment),
}

impl<Moment: AtLeast32BitUnsigned + Copy> AtOrAfter<Moment> {
	pub fn evaluate(&self, since: Moment) -> Moment {
		match &self {
			Self::At(m) => *m,
			Self::After(m) => m.saturating_add(since),
		}
	}
}

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct ReferendumStatus<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId> {
	/// The track of this referendum.
	pub(crate) track: TrackId,
	/// The origin for this referendum.
	pub(crate) origin: Origin,
	/// The hash of the proposal up for referendum.
	pub(crate) proposal_hash: Hash,
	/// The time the proposal should be scheduled for enactment.
	pub(crate) enactment: AtOrAfter<Moment>,
	/// The time of submission. Once `UndecidingTimeout` passes, it may be closed by anyone if it
	/// `deciding` is `None`.
	pub(crate) submitted: Moment,
	/// The deposit reserved for the submission of this referendum.
	pub(crate) submission_deposit: Deposit<AccountId, Balance>,
	/// The deposit reserved for this referendum to be decided.
	pub(crate) decision_deposit: Option<Deposit<AccountId, Balance>>,
	/// The status of a decision being made. If `None`, it has not entered the deciding period.
	pub(crate) deciding: Option<DecidingStatus<Moment>>,
	/// The current tally of votes in this referendum.
	pub(crate) tally: Tally,
	/// The number of aye votes we are in the track queue for, if any. `None` if we're not
	/// yet in the deciding queue or are already deciding. If a vote results in fewer ayes
	/// in the `tally` than this, then the voter is required to pay to reorder the track queue.
	/// Automatic advancement is scheduled when ayes_in_queue is Some value greater than the
	/// ayes in `tally`.
	pub(crate) ayes_in_queue: Option<Votes>,
}

impl<TrackId, Origin, Moment: AtLeast32BitUnsigned + Copy, Hash, Balance, Votes, Tally, AccountId>
	ReferendumStatus<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId>
{
	pub fn begin_deciding(&mut self, now: Moment, decision_period: Moment) {
		self.ayes_in_queue = None;
		self.deciding = Some(DecidingStatus {
			ending: now.saturating_add(decision_period),
			period: decision_period,
			confirming: None,
		});
	}
}

/// Info regarding a referendum, present or past.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum ReferendumInfo<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId> {
	/// Referendum has been submitted and is being voted on.
	Ongoing(ReferendumStatus<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId>),
	/// Referendum finished at `end` with approval. Submission deposit is held.
	Approved(Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished at `end` with rejection. Submission deposit is held.
	Rejected(Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
	/// Referendum finished at `end` and was never decided. Submission deposit is held.
	TimedOut(Deposit<AccountId, Balance>, Option<Deposit<AccountId, Balance>>),
}

impl<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId>
	ReferendumInfo<TrackId, Origin, Moment, Hash, Balance, Votes, Tally, AccountId>
{
	pub fn take_decision_deposit(&mut self) -> Option<Deposit<AccountId, Balance>> {
		use ReferendumInfo::*;
		match self {
			Approved(_, d) | Rejected(_, d) | TimedOut(_, d) => d.take(),
			// Cannot refund deposit if Ongoing as this breaks assumptions.
			_ => None,
		}
	}
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo)]
pub enum Curve {
	/// Linear curve starting at `(0, begin)`, ending at `(period, begin - delta)`.
	LinearDecreasing { begin: Perbill, delta: Perbill },
}

impl Curve {
	fn threshold(&self, x: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } => *begin - *delta * x,
		}
	}
	pub fn delay(&self, y: Perbill) -> Perbill {
		match self {
			Self::LinearDecreasing { begin, delta } => {
				(*begin - y.min(*begin)).min(*delta) / *delta
			},
		}
	}
	pub fn passing(&self, x: Perbill, y: Perbill) -> bool {
		y >= self.threshold(x)
	}
}
