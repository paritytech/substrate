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

//! The imbalance trait type and its associates, which handles keeps everything adding up properly
//! with unbalanced operations.

use sp_std::ops::Div;
use sp_runtime::traits::Saturating;
use crate::traits::misc::{TryDrop, SameOrOther};

mod split_two_ways;
mod signed_imbalance;
mod on_unbalanced;
pub use split_two_ways::SplitTwoWays;
pub use signed_imbalance::SignedImbalance;
pub use on_unbalanced::OnUnbalanced;

/// A trait for a not-quite Linear Type that tracks an imbalance.
///
/// Functions that alter account balances return an object of this trait to
/// express how much account balances have been altered in aggregate. If
/// dropped, the currency system will take some default steps to deal with
/// the imbalance (`balances` module simply reduces or increases its
/// total issuance). Your module should generally handle it in some way,
/// good practice is to do so in a configurable manner using an
/// `OnUnbalanced` type for each situation in which your module needs to
/// handle an imbalance.
///
/// Imbalances can either be Positive (funds were added somewhere without
/// being subtracted elsewhere - e.g. a reward) or Negative (funds deducted
/// somewhere without an equal and opposite addition - e.g. a slash or
/// system fee payment).
///
/// Since they are unsigned, the actual type is always Positive or Negative.
/// The trait makes no distinction except to define the `Opposite` type.
///
/// New instances of zero value can be created (`zero`) and destroyed
/// (`drop_zero`).
///
/// Existing instances can be `split` and merged either consuming `self` with
/// `merge` or mutating `self` with `subsume`. If the target is an `Option`,
/// then `maybe_merge` and `maybe_subsume` might work better. Instances can
/// also be `offset` with an `Opposite` that is less than or equal to in value.
///
/// You can always retrieve the raw balance value using `peek`.
#[must_use]
pub trait Imbalance<Balance>: Sized + TryDrop + Default {
	/// The oppositely imbalanced type. They come in pairs.
	type Opposite: Imbalance<Balance>;

	/// The zero imbalance. Can be destroyed with `drop_zero`.
	fn zero() -> Self;

	/// Drop an instance cleanly. Only works if its `self.value()` is zero.
	fn drop_zero(self) -> Result<(), Self>;

	/// Consume `self` and return two independent instances; the first
	/// is guaranteed to be at most `amount` and the second will be the remainder.
	fn split(self, amount: Balance) -> (Self, Self);

	/// Consume `self` and return two independent instances; the amounts returned will be in
	/// approximately the same ratio as `first`:`second`.
	///
	/// NOTE: This requires up to `first + second` room for a multiply, and `first + second` should
	/// fit into a `u32`. Overflow will safely saturate in both cases.
	fn ration(self, first: u32, second: u32) -> (Self, Self)
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let total: u32 = first.saturating_add(second);
		if total == 0 { return (Self::zero(), Self::zero()) }
		let amount1 = self.peek().saturating_mul(first.into()) / total.into();
		self.split(amount1)
	}

	/// Consume self and add its two components, defined by the first component's balance,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn split_merge(self, amount: Balance, others: (Self, Self)) -> (Self, Self) {
		let (a, b) = self.split(amount);
		(a.merge(others.0), b.merge(others.1))
	}

	/// Consume self and add its two components, defined by the ratio `first`:`second`,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn ration_merge(self, first: u32, second: u32, others: (Self, Self)) -> (Self, Self)
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let (a, b) = self.ration(first, second);
		(a.merge(others.0), b.merge(others.1))
	}

	/// Consume self and add its two components, defined by the first component's balance,
	/// element-wise into two pre-existing Imbalance refs.
	///
	/// A convenient replacement for `split` and `subsume`.
	fn split_merge_into(self, amount: Balance, others: &mut (Self, Self)) {
		let (a, b) = self.split(amount);
		others.0.subsume(a);
		others.1.subsume(b);
	}

	/// Consume self and add its two components, defined by the ratio `first`:`second`,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn ration_merge_into(self, first: u32, second: u32, others: &mut (Self, Self))
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let (a, b) = self.ration(first, second);
		others.0.subsume(a);
		others.1.subsume(b);
	}

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	fn merge(self, other: Self) -> Self;

	/// Consume self to mutate `other` so that it combines both. Just like `subsume`, only with
	/// reversed arguments.
	fn merge_into(self, other: &mut Self) {
		other.subsume(self)
	}

	/// Consume `self` and maybe an `other` to return a new instance that combines
	/// both.
	fn maybe_merge(self, other: Option<Self>) -> Self {
		if let Some(o) = other {
			self.merge(o)
		} else {
			self
		}
	}

	/// Consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn subsume(&mut self, other: Self);

	/// Maybe consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn maybe_subsume(&mut self, other: Option<Self>) {
		if let Some(o) = other {
			self.subsume(o)
		}
	}

	/// Consume self and along with an opposite counterpart to return
	/// a combined result.
	///
	/// Returns `Ok` along with a new instance of `Self` if this instance has a
	/// greater value than the `other`. Otherwise returns `Err` with an instance of
	/// the `Opposite`. In both cases the value represents the combination of `self`
	/// and `other`.
	fn offset(self, other: Self::Opposite)-> SameOrOther<Self, Self::Opposite>;

	/// The raw value of self.
	fn peek(&self) -> Balance;
}
