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

#![deny(missing_docs)]

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::Parameter;
use scale_info::TypeInfo;
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_core::RuntimeDebug;
use sp_std::{fmt::Debug, vec::Vec};

/// Index of a Polkadot Core.
pub type CoreIndex = u16;

/// A Task Id. In general this is called a ParachainId.
pub type TaskId = u32;

/// Fraction expressed as a nominator with an assumed denominator of 57,600.
pub type PartsOf57600 = u16;

/// An element to which a core can be assigned.
#[derive(
	Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub enum CoreAssignment {
	/// Core need not be used for anything.
	Idle,
	/// Core should be used for the Instantaneous Coretime Pool.
	Pool,
	/// Core should be used to process the given task.
	Task(TaskId),
}

/// Type able to accept Coretime scheduling instructions and provide certain usage information.
/// Generally implemented by the Relay-chain or some means of communicating with it.
///
/// The trait representation of RFC#5 `<https://github.com/polkadot-fellows/RFCs/pull/5>`.
pub trait CoretimeInterface {
	/// A (Relay-chain-side) account ID.
	type AccountId: Parameter;

	/// A (Relay-chain-side) balance.
	type Balance: AtLeast32BitUnsigned;

	/// A (Relay-chain-side) block number.
	type BlockNumber: AtLeast32BitUnsigned
		+ Copy
		+ TypeInfo
		+ Encode
		+ Decode
		+ MaxEncodedLen
		+ Debug;

	/// Return the latest block number on the Relay-chain.
	fn latest() -> Self::BlockNumber;

	/// Requests the Relay-chain to alter the number of schedulable cores to `count`. Under normal
	/// operation, the Relay-chain SHOULD send a `notify_core_count(count)` message back.
	fn request_core_count(count: CoreIndex);

	/// Requests that the Relay-chain send a `notify_revenue` message back at or soon after
	/// Relay-chain block number `when` whose `until` parameter is equal to `when`.
	///
	/// `when` may never be greater than the result of `Self::latest()`.
	/// The period in to the past which `when` is allowed to be may be limited; if so the limit
	/// should be understood on a channel outside of this proposal. In the case that the request
	/// cannot be serviced because `when` is too old a block then a `notify_revenue` message must
	/// still be returned, but its `revenue` field may be `None`.
	fn request_revenue_info_at(when: Self::BlockNumber);

	/// Instructs the Relay-chain to add the `amount` of DOT to the Instantaneous Coretime Market
	/// Credit account of `who`.
	///
	/// It is expected that Instantaneous Coretime Market Credit on the Relay-chain is NOT
	/// transferrable and only redeemable when used to assign cores in the Instantaneous Coretime
	/// Pool.
	fn credit_account(who: Self::AccountId, amount: Self::Balance);

	/// Instructs the Relay-chain to ensure that the core indexed as `core` is utilised for a number
	/// of assignments in specific ratios given by `assignment` starting as soon after `begin` as
	/// possible. Core assignments take the form of a `CoreAssignment` value which can either task
	/// the core to a `ParaId` value or indicate that the core should be used in the Instantaneous
	/// Pool. Each assignment comes with a ratio value, represented as the numerator of the fraction
	/// with a denominator of 57,600.
	///
	/// If `end_hint` is `Some` and the inner is greater than the current block number, then the
	/// Relay-chain should optimize in the expectation of receiving a new `assign_core(core, ...)`
	/// message at or prior to the block number of the inner value. Specific functionality should
	/// remain unchanged regardless of the `end_hint` value.
	fn assign_core(
		core: CoreIndex,
		begin: Self::BlockNumber,
		assignment: Vec<(CoreAssignment, PartsOf57600)>,
		end_hint: Option<Self::BlockNumber>,
	);

	/// Indicate that from this block onwards, the range of acceptable values of the `core`
	/// parameter of `assign_core` message is `[0, count)`. `assign_core` will be a no-op if
	/// provided with a value for `core` outside of this range.
	fn check_notify_core_count() -> Option<u16>;

	/// Provide the amount of revenue accumulated from Instantaneous Coretime Sales from Relay-chain
	/// block number `last_until` to `until`, not including `until` itself. `last_until` is defined
	/// as being the `until` argument of the last `notify_revenue` message sent, or zero for the
	/// first call. If `revenue` is `None`, this indicates that the information is no longer
	/// available.
	///
	/// This explicitly disregards the possibility of multiple parachains requesting and being
	/// notified of revenue information. The Relay-chain must be configured to ensure that only a
	/// single revenue information destination exists.
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)>;

	/// Ensure that core count is updated to the provided value.
	///
	/// This is only used for benchmarking.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_notify_core_count(count: u16);

	/// Ensure that revenue information is updated to the provided value.
	///
	/// This is only used for benchmarking.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_notify_revenue_info(when: Self::BlockNumber, revenue: Self::Balance);
}

impl CoretimeInterface for () {
	type AccountId = ();
	type Balance = u64;
	type BlockNumber = u32;
	fn latest() -> Self::BlockNumber {
		0
	}
	fn request_core_count(_count: CoreIndex) {}
	fn request_revenue_info_at(_when: Self::BlockNumber) {}
	fn credit_account(_who: Self::AccountId, _amount: Self::Balance) {}
	fn assign_core(
		_core: CoreIndex,
		_begin: Self::BlockNumber,
		_assignment: Vec<(CoreAssignment, PartsOf57600)>,
		_end_hint: Option<Self::BlockNumber>,
	) {
	}
	fn check_notify_core_count() -> Option<u16> {
		None
	}
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)> {
		None
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_notify_core_count(_count: u16) {}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_notify_revenue_info(_when: Self::BlockNumber, _revenue: Self::Balance) {}
}
