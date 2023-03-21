// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! The traits for dealing with a single fungible token class and any associated types.
//!
//! ### User-implememted traits
//! - `Inspect`: Regular balance inspector functions.
//! - `Unbalanced`: Low-level balance mutating functions. Does not guarantee proper book-keeping and
//!   so should not be called into directly from application code. Other traits depend on this and
//!   provide default implementations based on it.
//! - `UnbalancedHold`: Low-level balance mutating functions for balances placed on hold. Does not
//!   guarantee proper book-keeping and so should not be called into directly from application code.
//!   Other traits depend on this and provide default implementations based on it.
//! - `Mutate`: Regular balance mutator functions. Pre-implemented using `Unbalanced`, though the
//!   `done_*` functions should likely be reimplemented in case you want to do something following
//!   the operation such as emit events.
//! - `InspectHold`: Inspector functions for balances on hold.
//! - `MutateHold`: Mutator functions for balances on hold. Mostly pre-implemented using
//!   `UnbalancedHold`.
//! - `InspectFreeze`: Inspector functions for frozen balance.
//! - `MutateFreeze`: Mutator functions for frozen balance.
//! - `Balanced`: One-sided mutator functions for regular balances, which return imbalance objects
//!   which guarantee eventual book-keeping. May be useful for some sophisticated operations where
//!   funds must be removed from an account before it is known precisely what should be done with
//!   them.

pub mod freeze;
pub mod hold;
mod imbalance;
mod item_of;
mod regular;

pub use freeze::{Inspect as InspectFreeze, Mutate as MutateFreeze};
pub use hold::{
	Balanced as BalancedHold, Inspect as InspectHold, Mutate as MutateHold,
	Unbalanced as UnbalancedHold,
};
pub use imbalance::{Credit, Debt, HandleImbalanceDrop, Imbalance};
pub use item_of::ItemOf;
pub use regular::{
	Balanced, DecreaseIssuance, Dust, IncreaseIssuance, Inspect, Mutate, Unbalanced,
};
use sp_runtime::traits::Convert;

use crate::traits::{Consideration, Footprint};

pub struct FreezeConsideration<A, F, R, D>(sp_std::marker::PhantomData<(A, F, R, D)>);
impl<A, F: MutateFreeze<A>, R: F::Id, D: Convert<Footprint, F::Balance>> Consideration<A> for FreezeConsideration<A, F, R, D> {
	type Ticket = ();
	fn update(
		who: &A,
		_old: Option<Self::Ticket>,
		new: Option<Footprint>,
	) -> Result<Self::Ticket, sp_runtime::DispatchError> {
		match new {
			Some(footprint) => F::set_freeze(&R::get(), who, D::convert(footprint)),
			None => F::thaw(&R::get(), who),
		}
	}
}

pub struct HoldConsideration<A, F, R, D>(sp_std::marker::PhantomData<(A, F, R, D)>);
impl<A, F: MutateHold<A>, R: F::Id, D: Convert<Footprint, F::Balance>> Consideration<A> for HoldConsideration<A, F, R, D> {
	type Ticket = ();
	fn update(
		who: &A,
		_old: Option<Self::Ticket>,
		new: Option<Footprint>,
	) -> Result<Self::Ticket, sp_runtime::DispatchError> {
		match (old, new) {
			Some(footprint) => F::set_on_hold(&R::get(), who, D::convert(footprint)),
			None => F::release_all(&R::get(), who, super::Precision::BestEffort),
		}
	}
}