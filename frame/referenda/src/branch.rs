// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0sp_runtime::{DispatchResult, traits::One}asp_runtime::{DispatchResult, traits::AtLeast32BitUnsigned} in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Helpers for managing the different weights in various algorithmic branches.

use crate::weights::WeightInfo;
use super::Config;

pub enum BeginDecidingBranch {
	Passing,
	Failing,
}

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
		use {BeginDecidingBranch::*, ServiceBranch::*};
		match x {
			Passing => BeginDecidingPassing,
			Failing => BeginDecidingFailing,
		}
	}
}

impl ServiceBranch {
	pub fn weight_of_nudge<T: Config>(self) -> frame_support::weights::Weight {
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

	pub fn max_weight_of_nudge<T: Config>() -> frame_support::weights::Weight {
		0
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

	pub fn weight_of_deposit<T: Config>(self) -> Option<frame_support::weights::Weight> {
		use ServiceBranch::*;
		Some(match self {
			Preparing => T::WeightInfo::place_decision_deposit_preparing(),
			Queued => T::WeightInfo::place_decision_deposit_queued(),
			NotQueued => T::WeightInfo::place_decision_deposit_not_queued(),
			BeginDecidingPassing => T::WeightInfo::place_decision_deposit_passing(),
			BeginDecidingFailing => T::WeightInfo::place_decision_deposit_failing(),
			BeginConfirming | ContinueConfirming | EndConfirming | ContinueNotConfirming | Approved
			| Rejected | RequeuedInsertion | RequeuedSlide | TimedOut | Fail | NoDeposit
			=> return None,
		})
	}

	pub fn max_weight_of_deposit<T: Config>() -> frame_support::weights::Weight {
		0
			.max(T::WeightInfo::place_decision_deposit_preparing())
			.max(T::WeightInfo::place_decision_deposit_queued())
			.max(T::WeightInfo::place_decision_deposit_not_queued())
			.max(T::WeightInfo::place_decision_deposit_passing())
			.max(T::WeightInfo::place_decision_deposit_failing())
	}
}

pub enum OneFewerDecidingBranch {
	QueueEmpty,
	BeginDecidingPassing,
	BeginDecidingFailing,
}

impl From<BeginDecidingBranch> for OneFewerDecidingBranch {
	fn from(x: BeginDecidingBranch) -> Self {
		use {BeginDecidingBranch::*, OneFewerDecidingBranch::*};
		match x {
			Passing => BeginDecidingPassing,
			Failing => BeginDecidingFailing,
		}
	}
}

impl OneFewerDecidingBranch {
	pub fn weight<T: Config>(self) -> frame_support::weights::Weight {
		use OneFewerDecidingBranch::*;
		match self {
			QueueEmpty => T::WeightInfo::one_fewer_deciding_queue_empty(),
			BeginDecidingPassing => T::WeightInfo::one_fewer_deciding_passing(),
			BeginDecidingFailing => T::WeightInfo::one_fewer_deciding_failing(),
		}
	}

	pub fn max_weight<T: Config>() -> frame_support::weights::Weight {
		0
			.max(T::WeightInfo::one_fewer_deciding_queue_empty())
			.max(T::WeightInfo::one_fewer_deciding_passing())
			.max(T::WeightInfo::one_fewer_deciding_failing())
	}
}
