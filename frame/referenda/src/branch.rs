// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Helpers for managing the different weights in various algorithmic branches.

use super::Config;
use crate::weights::WeightInfo;
use frame_support::weights::Weight;

/// Branches within the `begin_deciding` function.
pub enum BeginDecidingBranch {
	Passing,
	Failing,
}

/// Branches within the `service_referendum` function.
pub enum ServiceBranch {
	Fail,
	NoDeposit,
	Preparing,
	Queued,
	NotQueued,
	RequeuedInsertion,
	RequeuedSlide,
	BeginDecidingPassing,
	BeginDecidingFailing,
	BeginConfirming,
	ContinueConfirming,
	EndConfirming,
	ContinueNotConfirming,
	Approved,
	Rejected,
	TimedOut,
}

impl From<BeginDecidingBranch> for ServiceBranch {
	fn from(x: BeginDecidingBranch) -> Self {
		use BeginDecidingBranch::*;
		use ServiceBranch::*;
		match x {
			Passing => BeginDecidingPassing,
			Failing => BeginDecidingFailing,
		}
	}
}

impl ServiceBranch {
	/// Return the weight of the `nudge` function when it takes the branch denoted by `self`.
	pub fn weight_of_nudge<T: Config<I>, I: 'static>(self) -> frame_support::weights::Weight {
		use ServiceBranch::*;
		match self {
			NoDeposit => T::WeightInfo::nudge_referendum_no_deposit(),
			Preparing => T::WeightInfo::nudge_referendum_preparing(),
			Queued => T::WeightInfo::nudge_referendum_queued(),
			NotQueued => T::WeightInfo::nudge_referendum_not_queued(),
			RequeuedInsertion => T::WeightInfo::nudge_referendum_requeued_insertion(),
			RequeuedSlide => T::WeightInfo::nudge_referendum_requeued_slide(),
			BeginDecidingPassing => T::WeightInfo::nudge_referendum_begin_deciding_passing(),
			BeginDecidingFailing => T::WeightInfo::nudge_referendum_begin_deciding_failing(),
			BeginConfirming => T::WeightInfo::nudge_referendum_begin_confirming(),
			ContinueConfirming => T::WeightInfo::nudge_referendum_continue_confirming(),
			EndConfirming => T::WeightInfo::nudge_referendum_end_confirming(),
			ContinueNotConfirming => T::WeightInfo::nudge_referendum_continue_not_confirming(),
			Approved => T::WeightInfo::nudge_referendum_approved(),
			Rejected => T::WeightInfo::nudge_referendum_rejected(),
			TimedOut | Fail => T::WeightInfo::nudge_referendum_timed_out(),
		}
	}

	/// Return the maximum possible weight of the `nudge` function.
	pub fn max_weight_of_nudge<T: Config<I>, I: 'static>() -> frame_support::weights::Weight {
		Weight::zero()
			.max(T::WeightInfo::nudge_referendum_no_deposit())
			.max(T::WeightInfo::nudge_referendum_preparing())
			.max(T::WeightInfo::nudge_referendum_queued())
			.max(T::WeightInfo::nudge_referendum_not_queued())
			.max(T::WeightInfo::nudge_referendum_requeued_insertion())
			.max(T::WeightInfo::nudge_referendum_requeued_slide())
			.max(T::WeightInfo::nudge_referendum_begin_deciding_passing())
			.max(T::WeightInfo::nudge_referendum_begin_deciding_failing())
			.max(T::WeightInfo::nudge_referendum_begin_confirming())
			.max(T::WeightInfo::nudge_referendum_continue_confirming())
			.max(T::WeightInfo::nudge_referendum_end_confirming())
			.max(T::WeightInfo::nudge_referendum_continue_not_confirming())
			.max(T::WeightInfo::nudge_referendum_approved())
			.max(T::WeightInfo::nudge_referendum_rejected())
			.max(T::WeightInfo::nudge_referendum_timed_out())
	}

	/// Return the weight of the `place_decision_deposit` function when it takes the branch denoted
	/// by `self`.
	pub fn weight_of_deposit<T: Config<I>, I: 'static>(
		self,
	) -> Option<frame_support::weights::Weight> {
		use ServiceBranch::*;
		let ref_time_weight = match self {
			Preparing => T::WeightInfo::place_decision_deposit_preparing(),
			Queued => T::WeightInfo::place_decision_deposit_queued(),
			NotQueued => T::WeightInfo::place_decision_deposit_not_queued(),
			BeginDecidingPassing => T::WeightInfo::place_decision_deposit_passing(),
			BeginDecidingFailing => T::WeightInfo::place_decision_deposit_failing(),
			BeginConfirming |
			ContinueConfirming |
			EndConfirming |
			ContinueNotConfirming |
			Approved |
			Rejected |
			RequeuedInsertion |
			RequeuedSlide |
			TimedOut |
			Fail |
			NoDeposit => return None,
		};

		Some(ref_time_weight)
	}

	/// Return the maximum possible weight of the `place_decision_deposit` function.
	pub fn max_weight_of_deposit<T: Config<I>, I: 'static>() -> frame_support::weights::Weight {
		Weight::zero()
			.max(T::WeightInfo::place_decision_deposit_preparing())
			.max(T::WeightInfo::place_decision_deposit_queued())
			.max(T::WeightInfo::place_decision_deposit_not_queued())
			.max(T::WeightInfo::place_decision_deposit_passing())
			.max(T::WeightInfo::place_decision_deposit_failing())
	}
}

/// Branches that the `one_fewer_deciding` function may take.
pub enum OneFewerDecidingBranch {
	QueueEmpty,
	BeginDecidingPassing,
	BeginDecidingFailing,
}

impl From<BeginDecidingBranch> for OneFewerDecidingBranch {
	fn from(x: BeginDecidingBranch) -> Self {
		use BeginDecidingBranch::*;
		use OneFewerDecidingBranch::*;
		match x {
			Passing => BeginDecidingPassing,
			Failing => BeginDecidingFailing,
		}
	}
}

impl OneFewerDecidingBranch {
	/// Return the weight of the `one_fewer_deciding` function when it takes the branch denoted
	/// by `self`.
	pub fn weight<T: Config<I>, I: 'static>(self) -> frame_support::weights::Weight {
		use OneFewerDecidingBranch::*;
		match self {
			QueueEmpty => T::WeightInfo::one_fewer_deciding_queue_empty(),
			BeginDecidingPassing => T::WeightInfo::one_fewer_deciding_passing(),
			BeginDecidingFailing => T::WeightInfo::one_fewer_deciding_failing(),
		}
	}

	/// Return the maximum possible weight of the `one_fewer_deciding` function.
	pub fn max_weight<T: Config<I>, I: 'static>() -> frame_support::weights::Weight {
		Weight::zero()
			.max(T::WeightInfo::one_fewer_deciding_queue_empty())
			.max(T::WeightInfo::one_fewer_deciding_passing())
			.max(T::WeightInfo::one_fewer_deciding_failing())
	}
}
