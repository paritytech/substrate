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

//! An implementation of a delegation system for nominators.
//!
//! This allows an account (called delegator) to delegate their funds to another account
//! (delegatee). Multiple delegators can delegate to the same delegatee. The delegatee is then able
//! to use the funds of all delegators to nominate a set of validators.

use std::ops::Sub;
use codec::{FullCodec, MaxEncodedLen};
use scale_info::TypeInfo;
use frame_support::dispatch::DispatchResult;
use sp_runtime::Saturating;
use crate::{BalanceOf, Config};

/// A ledger of a delegator.
///
/// This keeps track of the active balance of the delegator that is made up from the funds that are
/// currently delegated to a delegatee. It also tracks the slashes yet to be applied.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct DelegationLedger<T: Config> {
	/// Sum of all delegated funds to this delegatee.
	pub balance: BalanceOf<T>,
	/// Slashes that are not yet applied.
	pub pending_slash: BalanceOf<T>,
}

/// A generic representation of a delegation apis exposed by staking pallet for use by other runtime
/// pallets.
pub trait DelegationInterface {
	/// AccountId type used by the runtime.
	type AccountId: Clone + sp_std::fmt::Debug;

	/// Balance type used by the runtime.
	type Balance: Sub<Output = Self::Balance>
	+ Ord
	+ PartialEq
	+ Default
	+ Copy
	+ MaxEncodedLen
	+ FullCodec
	+ TypeInfo
	+ Saturating;

	/// Delegate some funds or add to an existing delegation.
	// TODO(ank4n): No restriction to number of delegations per delegator?
	fn delegate(delegator: Self::AccountId, delegatee: Self::AccountId, value: Self::Balance) -> DispatchResult;
	/// Remove delegation of some or all funds.
	fn remove_delegate(delegator: Self::AccountId, delegatee: Self::AccountId, value: Self::Balance) -> DispatchResult;
}
