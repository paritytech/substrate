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

//! Smaller traits used in FRAME which don't need their own file.

use crate::dispatch::{DispatchResult, Parameter};
use codec::{CompactLen, Decode, DecodeLimit, Encode, EncodeLike, Input, MaxEncodedLen};
use impl_trait_for_tuples::impl_for_tuples;
use scale_info::{build::Fields, meta_type, Path, Type, TypeInfo, TypeParameter};
use sp_arithmetic::traits::{CheckedAdd, CheckedMul, CheckedSub, One, Saturating};
use sp_core::bounded::bounded_vec::TruncateFrom;
#[doc(hidden)]
pub use sp_runtime::traits::{
	ConstBool, ConstI128, ConstI16, ConstI32, ConstI64, ConstI8, ConstU128, ConstU16, ConstU32,
	ConstU64, ConstU8, Get, GetDefault, TryCollect, TypedGet,
};
use sp_runtime::{traits::Block as BlockT, DispatchError};
use sp_std::{cmp::Ordering, prelude::*};

#[doc(hidden)]
pub const DEFENSIVE_OP_PUBLIC_ERROR: &str = "a defensive failure has been triggered; please report the block number at https://github.com/paritytech/substrate/issues";
#[doc(hidden)]
pub const DEFENSIVE_OP_INTERNAL_ERROR: &str = "Defensive failure has been triggered!";

/// Generic function to mark an execution path as ONLY defensive.
///
/// Similar to mark a match arm or `if/else` branch as `unreachable!`.
#[macro_export]
macro_rules! defensive {
	() => {
		frame_support::__private::log::error!(
			target: "runtime",
			"{}",
			$crate::traits::DEFENSIVE_OP_PUBLIC_ERROR
		);
		debug_assert!(false, "{}", $crate::traits::DEFENSIVE_OP_INTERNAL_ERROR);
	};
	($error:expr $(,)?) => {
		frame_support::__private::log::error!(
			target: "runtime",
			"{}: {:?}",
			$crate::traits::DEFENSIVE_OP_PUBLIC_ERROR,
			$error
		);
		debug_assert!(false, "{}: {:?}", $crate::traits::DEFENSIVE_OP_INTERNAL_ERROR, $error);
	};
	($error:expr, $proof:expr $(,)?) => {
		frame_support::__private::log::error!(
			target: "runtime",
			"{}: {:?}: {:?}",
			$crate::traits::DEFENSIVE_OP_PUBLIC_ERROR,
			$error,
			$proof,
		);
		debug_assert!(false, "{}: {:?}: {:?}", $crate::traits::DEFENSIVE_OP_INTERNAL_ERROR, $error, $proof);
	}
}

/// Trigger a defensive failure if a condition is not met.
///
/// Similar to [`assert!`] but will print an error without `debug_assertions` instead of silently
/// ignoring it. Only accepts one instead of variable formatting arguments.
///
/// # Example
///
/// ```should_panic
/// frame_support::defensive_assert!(1 == 0, "Must fail")
/// ```
#[macro_export]
macro_rules! defensive_assert {
	($cond:expr $(, $proof:expr )? $(,)?) => {
		if !($cond) {
			$crate::defensive!(::core::stringify!($cond) $(, $proof )?);
		}
	};
}

/// Prelude module for all defensive traits to be imported at once.
pub mod defensive_prelude {
	pub use super::{Defensive, DefensiveOption, DefensiveResult};
}

/// A trait to handle errors and options when you are really sure that a condition must hold, but
/// not brave enough to `expect` on it, or a default fallback value makes more sense.
///
/// This trait mostly focuses on methods that eventually unwrap the inner value. See
/// [`DefensiveResult`] and [`DefensiveOption`] for methods that specifically apply to the
/// respective types.
///
/// Each function in this trait will have two side effects, aside from behaving exactly as the name
/// would suggest:
///
/// 1. It panics on `#[debug_assertions]`, so if the infallible code is reached in any of the tests,
///    you realize.
/// 2. It will log an error using the runtime logging system. This might help you detect such bugs
///    in production as well. Note that the log message, as of now, are not super expressive. Your
///    best shot of fully diagnosing the error would be to infer the block number of which the log
///    message was emitted, then re-execute that block using `check-block` or `try-runtime`
///    subcommands in substrate client.
pub trait Defensive<T> {
	/// Exactly the same as `unwrap_or`, but it does the defensive warnings explained in the trait
	/// docs.
	fn defensive_unwrap_or(self, other: T) -> T;

	/// Exactly the same as `unwrap_or_else`, but it does the defensive warnings explained in the
	/// trait docs.
	fn defensive_unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T;

	/// Exactly the same as `unwrap_or_default`, but it does the defensive warnings explained in the
	/// trait docs.
	fn defensive_unwrap_or_default(self) -> T
	where
		T: Default;

	/// Does not alter the inner value at all, but it will log warnings if the inner value is `None`
	/// or `Err`.
	///
	/// In some ways, this is like  `.defensive_map(|x| x)`.
	///
	/// This is useful as:
	/// ```nocompile
	/// if let Some(inner) = maybe_value().defensive() {
	/// 	 	..
	/// }
	/// ```
	fn defensive(self) -> Self;

	/// Same as [`Defensive::defensive`], but it takes a proof as input, and displays it if the
	/// defensive operation has been triggered.
	fn defensive_proof(self, proof: &'static str) -> Self;
}

/// Subset of methods similar to [`Defensive`] that can only work for a `Result`.
pub trait DefensiveResult<T, E> {
	/// Defensively map the error into another return type, but you are really sure that this
	/// conversion should never be needed.
	fn defensive_map_err<F, O: FnOnce(E) -> F>(self, o: O) -> Result<T, F>;

	/// Defensively map and unpack the value to something else (`U`), or call the default callback
	/// if `Err`, which should never happen.
	fn defensive_map_or_else<U, D: FnOnce(E) -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U;

	/// Defensively transform this result into an option, discarding the `Err` variant if it
	/// happens, which should never happen.
	fn defensive_ok(self) -> Option<T>;

	/// Exactly the same as `map`, but it prints the appropriate warnings if the value being mapped
	/// is `Err`.
	fn defensive_map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;
}

/// Subset of methods similar to [`Defensive`] that can only work for a `Option`.
pub trait DefensiveOption<T> {
	/// Potentially map and unpack the value to something else (`U`), or call the default callback
	/// if `None`, which should never happen.
	fn defensive_map_or_else<U, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U;

	/// Defensively transform this option to a result, mapping `None` to the return value of an
	/// error closure.
	fn defensive_ok_or_else<E: sp_std::fmt::Debug, F: FnOnce() -> E>(self, err: F) -> Result<T, E>;

	/// Defensively transform this option to a result, mapping `None` to a default value.
	fn defensive_ok_or<E: sp_std::fmt::Debug>(self, err: E) -> Result<T, E>;

	/// Exactly the same as `map`, but it prints the appropriate warnings if the value being mapped
	/// is `None`.
	fn defensive_map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;
}

impl<T> Defensive<T> for Option<T> {
	fn defensive_unwrap_or(self, or: T) -> T {
		match self {
			Some(inner) => inner,
			None => {
				defensive!();
				or
			},
		}
	}

	fn defensive_unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
		match self {
			Some(inner) => inner,
			None => {
				defensive!();
				f()
			},
		}
	}

	fn defensive_unwrap_or_default(self) -> T
	where
		T: Default,
	{
		match self {
			Some(inner) => inner,
			None => {
				defensive!();
				Default::default()
			},
		}
	}

	fn defensive(self) -> Self {
		match self {
			Some(inner) => Some(inner),
			None => {
				defensive!();
				None
			},
		}
	}

	fn defensive_proof(self, proof: &'static str) -> Self {
		if self.is_none() {
			defensive!(proof);
		}
		self
	}
}

impl<T, E: sp_std::fmt::Debug> Defensive<T> for Result<T, E> {
	fn defensive_unwrap_or(self, or: T) -> T {
		match self {
			Ok(inner) => inner,
			Err(e) => {
				defensive!(e);
				or
			},
		}
	}

	fn defensive_unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
		match self {
			Ok(inner) => inner,
			Err(e) => {
				defensive!(e);
				f()
			},
		}
	}

	fn defensive_unwrap_or_default(self) -> T
	where
		T: Default,
	{
		match self {
			Ok(inner) => inner,
			Err(e) => {
				defensive!(e);
				Default::default()
			},
		}
	}

	fn defensive(self) -> Self {
		match self {
			Ok(inner) => Ok(inner),
			Err(e) => {
				defensive!(e);
				Err(e)
			},
		}
	}

	fn defensive_proof(self, proof: &'static str) -> Self {
		match self {
			Ok(inner) => Ok(inner),
			Err(e) => {
				defensive!(e, proof);
				Err(e)
			},
		}
	}
}

impl<T, E: sp_std::fmt::Debug> DefensiveResult<T, E> for Result<T, E> {
	fn defensive_map_err<F, O: FnOnce(E) -> F>(self, o: O) -> Result<T, F> {
		self.map_err(|e| {
			defensive!(e);
			o(e)
		})
	}

	fn defensive_map_or_else<U, D: FnOnce(E) -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
		self.map_or_else(
			|e| {
				defensive!(e);
				default(e)
			},
			f,
		)
	}

	fn defensive_ok(self) -> Option<T> {
		match self {
			Ok(inner) => Some(inner),
			Err(e) => {
				defensive!(e);
				None
			},
		}
	}

	fn defensive_map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E> {
		match self {
			Ok(inner) => Ok(f(inner)),
			Err(e) => {
				defensive!(e);
				Err(e)
			},
		}
	}
}

impl<T> DefensiveOption<T> for Option<T> {
	fn defensive_map_or_else<U, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
		self.map_or_else(
			|| {
				defensive!();
				default()
			},
			f,
		)
	}

	fn defensive_ok_or_else<E: sp_std::fmt::Debug, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
		self.ok_or_else(|| {
			let err_value = err();
			defensive!(err_value);
			err_value
		})
	}

	fn defensive_ok_or<E: sp_std::fmt::Debug>(self, err: E) -> Result<T, E> {
		self.ok_or_else(|| {
			defensive!(err);
			err
		})
	}

	fn defensive_map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U> {
		match self {
			Some(inner) => Some(f(inner)),
			None => {
				defensive!();
				None
			},
		}
	}
}

/// A variant of [`Defensive`] with the same rationale, for the arithmetic operations where in
/// case an infallible operation fails, it saturates.
pub trait DefensiveSaturating {
	/// Return `self` plus `other` defensively.
	fn defensive_saturating_add(self, other: Self) -> Self;
	/// Return `self` minus `other` defensively.
	fn defensive_saturating_sub(self, other: Self) -> Self;
	/// Return the product of `self` and `other` defensively.
	fn defensive_saturating_mul(self, other: Self) -> Self;
	/// Increase `self` by `other` defensively.
	fn defensive_saturating_accrue(&mut self, other: Self);
	/// Reduce `self` by `other` defensively.
	fn defensive_saturating_reduce(&mut self, other: Self);
	/// Increment `self` by one defensively.
	fn defensive_saturating_inc(&mut self);
	/// Decrement `self` by one defensively.
	fn defensive_saturating_dec(&mut self);
}

// NOTE: A bit unfortunate, since T has to be bound by all the traits needed. Could make it
// `DefensiveSaturating<T>` to mitigate.
impl<T: Saturating + CheckedAdd + CheckedMul + CheckedSub + One> DefensiveSaturating for T {
	fn defensive_saturating_add(self, other: Self) -> Self {
		self.checked_add(&other).defensive_unwrap_or_else(|| self.saturating_add(other))
	}
	fn defensive_saturating_sub(self, other: Self) -> Self {
		self.checked_sub(&other).defensive_unwrap_or_else(|| self.saturating_sub(other))
	}
	fn defensive_saturating_mul(self, other: Self) -> Self {
		self.checked_mul(&other).defensive_unwrap_or_else(|| self.saturating_mul(other))
	}
	fn defensive_saturating_accrue(&mut self, other: Self) {
		// Use `replace` here since `take` would require `T: Default`.
		*self = sp_std::mem::replace(self, One::one()).defensive_saturating_add(other);
	}
	fn defensive_saturating_reduce(&mut self, other: Self) {
		// Use `replace` here since `take` would require `T: Default`.
		*self = sp_std::mem::replace(self, One::one()).defensive_saturating_sub(other);
	}
	fn defensive_saturating_inc(&mut self) {
		self.defensive_saturating_accrue(One::one());
	}
	fn defensive_saturating_dec(&mut self) {
		self.defensive_saturating_reduce(One::one());
	}
}

/// Construct an object by defensively truncating an input if the `TryFrom` conversion fails.
pub trait DefensiveTruncateFrom<T> {
	/// Use `TryFrom` first and defensively fall back to truncating otherwise.
	///
	/// # Example
	///
	/// ```
	/// use frame_support::{BoundedVec, traits::DefensiveTruncateFrom};
	/// use sp_runtime::traits::ConstU32;
	///
	/// let unbound = vec![1, 2];
	/// let bound = BoundedVec::<u8, ConstU32<2>>::defensive_truncate_from(unbound);
	///
	/// assert_eq!(bound, vec![1, 2]);
	/// ```
	fn defensive_truncate_from(unbound: T) -> Self;
}

impl<T, U> DefensiveTruncateFrom<U> for T
where
	// NOTE: We use the fact that `BoundedVec` and
	// `BoundedSlice` use `Self` as error type. We could also
	// require a `Clone` bound and use `unbound.clone()` in the
	// error case.
	T: TruncateFrom<U> + TryFrom<U, Error = U>,
{
	fn defensive_truncate_from(unbound: U) -> Self {
		unbound.try_into().map_or_else(
			|err| {
				defensive!("DefensiveTruncateFrom truncating");
				T::truncate_from(err)
			},
			|bound| bound,
		)
	}
}

/// Defensively calculates the minimum of two values.
///
/// Can be used in contexts where we assume the receiver value to be (strictly) smaller.
pub trait DefensiveMin<T> {
	/// Returns the minimum and defensively checks that `self` is not larger than `other`.
	///
	/// # Example
	///
	/// ```
	/// use frame_support::traits::DefensiveMin;
	/// // min(3, 4) is 3.
	/// assert_eq!(3, 3_u32.defensive_min(4_u32));
	/// // min(4, 4) is 4.
	/// assert_eq!(4, 4_u32.defensive_min(4_u32));
	/// ```
	///
	/// ```#[cfg_attr(debug_assertions, should_panic)]
	/// use frame_support::traits::DefensiveMin;
	/// // min(4, 3) panics.
	/// 4_u32.defensive_min(3_u32);
	/// ```
	fn defensive_min(self, other: T) -> Self;

	/// Returns the minimum and defensively checks that `self` is smaller than `other`.
	///
	/// # Example
	///
	/// ```
	/// use frame_support::traits::DefensiveMin;
	/// // min(3, 4) is 3.
	/// assert_eq!(3, 3_u32.defensive_strict_min(4_u32));
	/// ```
	///
	/// ```#[cfg_attr(debug_assertions, should_panic)]
	/// use frame_support::traits::DefensiveMin;
	/// // min(4, 4) panics.
	/// 4_u32.defensive_strict_min(4_u32);
	/// ```
	fn defensive_strict_min(self, other: T) -> Self;
}

impl<T> DefensiveMin<T> for T
where
	T: sp_std::cmp::PartialOrd<T>,
{
	fn defensive_min(self, other: T) -> Self {
		if self <= other {
			self
		} else {
			defensive!("DefensiveMin");
			other
		}
	}

	fn defensive_strict_min(self, other: T) -> Self {
		if self < other {
			self
		} else {
			defensive!("DefensiveMin strict");
			other
		}
	}
}

/// Defensively calculates the maximum of two values.
///
/// Can be used in contexts where we assume the receiver value to be (strictly) larger.
pub trait DefensiveMax<T> {
	/// Returns the maximum and defensively asserts that `other` is not larger than `self`.
	///
	/// # Example
	///
	/// ```
	/// use frame_support::traits::DefensiveMax;
	/// // max(4, 3) is 4.
	/// assert_eq!(4, 4_u32.defensive_max(3_u32));
	/// // max(4, 4) is 4.
	/// assert_eq!(4, 4_u32.defensive_max(4_u32));
	/// ```
	///
	/// ```#[cfg_attr(debug_assertions, should_panic)]
	/// use frame_support::traits::DefensiveMax;
	/// // max(4, 5) panics.
	/// 4_u32.defensive_max(5_u32);
	/// ```
	fn defensive_max(self, other: T) -> Self;

	/// Returns the maximum and defensively asserts that `other` is smaller than `self`.
	///
	/// # Example
	///
	/// ```
	/// use frame_support::traits::DefensiveMax;
	/// // y(4, 3) is 4.
	/// assert_eq!(4, 4_u32.defensive_strict_max(3_u32));
	/// ```
	///
	/// ```#[cfg_attr(debug_assertions, should_panic)]
	/// use frame_support::traits::DefensiveMax;
	/// // max(4, 4) panics.
	/// 4_u32.defensive_strict_max(4_u32);
	/// ```
	fn defensive_strict_max(self, other: T) -> Self;
}

impl<T> DefensiveMax<T> for T
where
	T: sp_std::cmp::PartialOrd<T>,
{
	fn defensive_max(self, other: T) -> Self {
		if self >= other {
			self
		} else {
			defensive!("DefensiveMax");
			other
		}
	}

	fn defensive_strict_max(self, other: T) -> Self {
		if self > other {
			self
		} else {
			defensive!("DefensiveMax strict");
			other
		}
	}
}

/// Anything that can have a `::len()` method.
pub trait Len {
	/// Return the length of data type.
	fn len(&self) -> usize;
}

impl<T: IntoIterator + Clone> Len for T
where
	<T as IntoIterator>::IntoIter: ExactSizeIterator,
{
	fn len(&self) -> usize {
		self.clone().into_iter().len()
	}
}

/// A type for which some values make sense to be able to drop without further consideration.
pub trait TryDrop: Sized {
	/// Drop an instance cleanly. Only works if its value represents "no-operation".
	fn try_drop(self) -> Result<(), Self>;
}

impl TryDrop for () {
	fn try_drop(self) -> Result<(), Self> {
		Ok(())
	}
}

/// Return type used when we need to return one of two items, each of the opposite direction or
/// sign, with one (`Same`) being of the same type as the `self` or primary argument of the function
/// that returned it.
pub enum SameOrOther<A, B> {
	/// No item.
	None,
	/// An item of the same type as the `Self` on which the return function was called.
	Same(A),
	/// An item of the opposite type to the `Self` on which the return function was called.
	Other(B),
}

impl<A, B> TryDrop for SameOrOther<A, B> {
	fn try_drop(self) -> Result<(), Self> {
		if let SameOrOther::None = self {
			Ok(())
		} else {
			Err(self)
		}
	}
}

impl<A, B> SameOrOther<A, B> {
	/// Returns `Ok` with the inner value of `Same` if `self` is that, otherwise returns `Err` with
	/// `self`.
	pub fn try_same(self) -> Result<A, Self> {
		match self {
			SameOrOther::Same(a) => Ok(a),
			x => Err(x),
		}
	}

	/// Returns `Ok` with the inner value of `Other` if `self` is that, otherwise returns `Err` with
	/// `self`.
	pub fn try_other(self) -> Result<B, Self> {
		match self {
			SameOrOther::Other(b) => Ok(b),
			x => Err(x),
		}
	}

	/// Returns `Ok` if `self` is `None`, otherwise returns `Err` with `self`.
	pub fn try_none(self) -> Result<(), Self> {
		match self {
			SameOrOther::None => Ok(()),
			x => Err(x),
		}
	}

	pub fn same(self) -> Result<A, B>
	where
		A: Default,
	{
		match self {
			SameOrOther::Same(a) => Ok(a),
			SameOrOther::None => Ok(A::default()),
			SameOrOther::Other(b) => Err(b),
		}
	}

	pub fn other(self) -> Result<B, A>
	where
		B: Default,
	{
		match self {
			SameOrOther::Same(a) => Err(a),
			SameOrOther::None => Ok(B::default()),
			SameOrOther::Other(b) => Ok(b),
		}
	}
}

/// Handler for when a new account has been created.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnNewAccount<AccountId> {
	/// A new account `who` has been registered.
	fn on_new_account(who: &AccountId);
}

/// The account with the given id was reaped.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnKilledAccount<AccountId> {
	/// The account with the given id was reaped.
	fn on_killed_account(who: &AccountId);
}

/// A simple, generic one-parameter event notifier/handler.
pub trait HandleLifetime<T> {
	/// An account was created.
	fn created(_t: &T) -> Result<(), DispatchError> {
		Ok(())
	}

	/// An account was killed.
	fn killed(_t: &T) -> Result<(), DispatchError> {
		Ok(())
	}
}

impl<T> HandleLifetime<T> for () {}

pub trait Time {
	type Moment: sp_arithmetic::traits::AtLeast32Bit + Parameter + Default + Copy + MaxEncodedLen;

	fn now() -> Self::Moment;
}

/// Trait to deal with unix time.
pub trait UnixTime {
	/// Return duration since `SystemTime::UNIX_EPOCH`.
	fn now() -> core::time::Duration;
}

/// Trait to be used when types are exactly same.
///
/// This allow to convert back and forth from type, a reference and a mutable reference.
pub trait IsType<T>: Into<T> + From<T> {
	/// Cast reference.
	fn from_ref(t: &T) -> &Self;

	/// Cast reference.
	fn into_ref(&self) -> &T;

	/// Cast mutable reference.
	fn from_mut(t: &mut T) -> &mut Self;

	/// Cast mutable reference.
	fn into_mut(&mut self) -> &mut T;
}

impl<T> IsType<T> for T {
	fn from_ref(t: &T) -> &Self {
		t
	}
	fn into_ref(&self) -> &T {
		self
	}
	fn from_mut(t: &mut T) -> &mut Self {
		t
	}
	fn into_mut(&mut self) -> &mut T {
		self
	}
}

/// Something that can be checked to be a of sub type `T`.
///
/// This is useful for enums where each variant encapsulates a different sub type, and
/// you need access to these sub types.
///
/// For example, in FRAME, this trait is implemented for the runtime `Call` enum. Pallets use this
/// to check if a certain call is an instance of the local pallet's `Call` enum.
///
/// # Example
///
/// ```
/// # use frame_support::traits::IsSubType;
///
/// enum Test {
///     String(String),
///     U32(u32),
/// }
///
/// impl IsSubType<String> for Test {
///     fn is_sub_type(&self) -> Option<&String> {
///         match self {
///             Self::String(ref r) => Some(r),
///             _ => None,
///         }
///     }
/// }
///
/// impl IsSubType<u32> for Test {
///     fn is_sub_type(&self) -> Option<&u32> {
///         match self {
///             Self::U32(ref r) => Some(r),
///             _ => None,
///         }
///     }
/// }
///
/// fn main() {
///     let data = Test::String("test".into());
///
///     assert_eq!("test", IsSubType::<String>::is_sub_type(&data).unwrap().as_str());
/// }
/// ```
pub trait IsSubType<T> {
	/// Returns `Some(_)` if `self` is an instance of sub type `T`.
	fn is_sub_type(&self) -> Option<&T>;
}

/// Something that can execute a given block.
///
/// Executing a block means that all extrinsics in a given block will be executed and the resulting
/// header will be checked against the header of the given block.
pub trait ExecuteBlock<Block: BlockT> {
	/// Execute the given `block`.
	///
	/// This will execute all extrinsics in the block and check that the resulting header is
	/// correct.
	///
	/// # Panic
	///
	/// Panics when an extrinsics panics or the resulting header doesn't match the expected header.
	fn execute_block(block: Block);
}

/// Something that can compare privileges of two origins.
pub trait PrivilegeCmp<Origin> {
	/// Compare the `left` to the `right` origin.
	///
	/// The returned ordering should be from the pov of the `left` origin.
	///
	/// Should return `None` when it can not compare the given origins.
	fn cmp_privilege(left: &Origin, right: &Origin) -> Option<Ordering>;
}

/// Implementation of [`PrivilegeCmp`] that only checks for equal origins.
///
/// This means it will either return [`Ordering::Equal`] or `None`.
pub struct EqualPrivilegeOnly;
impl<Origin: PartialEq> PrivilegeCmp<Origin> for EqualPrivilegeOnly {
	fn cmp_privilege(left: &Origin, right: &Origin) -> Option<Ordering> {
		(left == right).then(|| Ordering::Equal)
	}
}

/// Off-chain computation trait.
///
/// Implementing this trait on a module allows you to perform long-running tasks
/// that make (by default) validators generate transactions that feed results
/// of those long-running computations back on chain.
///
/// NOTE: This function runs off-chain, so it can access the block state,
/// but cannot preform any alterations. More specifically alterations are
/// not forbidden, but they are not persisted in any way after the worker
/// has finished.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OffchainWorker<BlockNumber> {
	/// This function is being called after every block import (when fully synced).
	///
	/// Implement this and use any of the `Offchain` `sp_io` set of APIs
	/// to perform off-chain computations, calls and submit transactions
	/// with results to trigger any on-chain changes.
	/// Any state alterations are lost and are not persisted.
	fn offchain_worker(_n: BlockNumber) {}
}

/// Some amount of backing from a group. The precise definition of what it means to "back" something
/// is left flexible.
pub struct Backing {
	/// The number of members of the group that back some motion.
	pub approvals: u32,
	/// The total count of group members.
	pub eligible: u32,
}

/// Retrieve the backing from an object's ref.
pub trait GetBacking {
	/// Returns `Some` `Backing` if `self` represents a fractional/groupwise backing of some
	/// implicit motion. `None` if it does not.
	fn get_backing(&self) -> Option<Backing>;
}

/// A trait to ensure the inherent are before non-inherent in a block.
///
/// This is typically implemented on runtime, through `construct_runtime!`.
pub trait EnsureInherentsAreFirst<Block> {
	/// Ensure the position of inherent is correct, i.e. they are before non-inherents.
	///
	/// On error return the index of the inherent with invalid position (counting from 0).
	fn ensure_inherents_are_first(block: &Block) -> Result<(), u32>;
}

/// An extrinsic on which we can get access to call.
pub trait ExtrinsicCall: sp_runtime::traits::Extrinsic {
	/// Get the call of the extrinsic.
	fn call(&self) -> &Self::Call;
}

#[cfg(feature = "std")]
impl<Call, Extra> ExtrinsicCall for sp_runtime::testing::TestXt<Call, Extra>
where
	Call: codec::Codec + Sync + Send + TypeInfo,
	Extra: TypeInfo,
{
	fn call(&self) -> &Self::Call {
		&self.call
	}
}

impl<Address, Call, Signature, Extra> ExtrinsicCall
	for sp_runtime::generic::UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Address: TypeInfo,
	Call: TypeInfo,
	Signature: TypeInfo,
	Extra: sp_runtime::traits::SignedExtension + TypeInfo,
{
	fn call(&self) -> &Self::Call {
		&self.function
	}
}

/// Something that can estimate the fee of a (frame-based) call.
///
/// Typically, the same pallet that will charge transaction fees will implement this.
pub trait EstimateCallFee<Call, Balance> {
	/// Estimate the fee of this call.
	///
	/// The dispatch info and the length is deduced from the call. The post info can optionally be
	/// provided.
	fn estimate_call_fee(call: &Call, post_info: crate::dispatch::PostDispatchInfo) -> Balance;
}

// Useful for building mocks.
#[cfg(feature = "std")]
impl<Call, Balance: From<u32>, const T: u32> EstimateCallFee<Call, Balance> for ConstU32<T> {
	fn estimate_call_fee(_: &Call, _: crate::dispatch::PostDispatchInfo) -> Balance {
		T.into()
	}
}

/// A wrapper for any type `T` which implement encode/decode in a way compatible with `Vec<u8>`.
///
/// The encoding is the encoding of `T` prepended with the compact encoding of its size in bytes.
/// Thus the encoded value can be decoded as a `Vec<u8>`.
#[derive(Debug, Eq, PartialEq, Default, Clone)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct WrapperOpaque<T>(pub T);

impl<T: Encode> EncodeLike for WrapperOpaque<T> {}
impl<T: Encode> EncodeLike<WrapperKeepOpaque<T>> for WrapperOpaque<T> {}

impl<T: Encode> Encode for WrapperOpaque<T> {
	fn size_hint(&self) -> usize {
		self.0.size_hint().saturating_add(<codec::Compact<u32>>::max_encoded_len())
	}

	fn encode_to<O: codec::Output + ?Sized>(&self, dest: &mut O) {
		self.0.encode().encode_to(dest);
	}

	fn encode(&self) -> Vec<u8> {
		self.0.encode().encode()
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.encode().using_encoded(f)
	}
}

impl<T: Decode> Decode for WrapperOpaque<T> {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		Ok(Self(T::decode_all_with_depth_limit(
			sp_api::MAX_EXTRINSIC_DEPTH,
			&mut &<Vec<u8>>::decode(input)?[..],
		)?))
	}

	fn skip<I: Input>(input: &mut I) -> Result<(), codec::Error> {
		<Vec<u8>>::skip(input)
	}
}

impl<T> From<T> for WrapperOpaque<T> {
	fn from(t: T) -> Self {
		Self(t)
	}
}

impl<T: MaxEncodedLen> MaxEncodedLen for WrapperOpaque<T> {
	fn max_encoded_len() -> usize {
		let t_max_len = T::max_encoded_len();

		// See scale encoding: https://docs.substrate.io/reference/scale-codec/
		if t_max_len < 64 {
			t_max_len + 1
		} else if t_max_len < 2usize.pow(14) {
			t_max_len + 2
		} else if t_max_len < 2usize.pow(30) {
			t_max_len + 4
		} else {
			<codec::Compact<u32>>::max_encoded_len().saturating_add(T::max_encoded_len())
		}
	}
}

impl<T: TypeInfo + 'static> TypeInfo for WrapperOpaque<T> {
	type Identity = Self;
	fn type_info() -> Type {
		Type::builder()
			.path(Path::new("WrapperOpaque", module_path!()))
			.type_params(vec![TypeParameter::new("T", Some(meta_type::<T>()))])
			.composite(
				Fields::unnamed()
					.field(|f| f.compact::<u32>())
					.field(|f| f.ty::<T>().type_name("T")),
			)
	}
}

/// A wrapper for any type `T` which implement encode/decode in a way compatible with `Vec<u8>`.
///
/// This type is similar to [`WrapperOpaque`], but it differs in the way it stores the type `T`.
/// While [`WrapperOpaque`] stores the decoded type, the [`WrapperKeepOpaque`] stores the type only
/// in its opaque format, aka as a `Vec<u8>`. To access the real type `T` [`Self::try_decode`] needs
/// to be used.
#[derive(Debug, Eq, PartialEq, Default, Clone)]
pub struct WrapperKeepOpaque<T> {
	data: Vec<u8>,
	_phantom: sp_std::marker::PhantomData<T>,
}

impl<T: Decode> WrapperKeepOpaque<T> {
	/// Try to decode the wrapped type from the inner `data`.
	///
	/// Returns `None` if the decoding failed.
	pub fn try_decode(&self) -> Option<T> {
		T::decode_all_with_depth_limit(sp_api::MAX_EXTRINSIC_DEPTH, &mut &self.data[..]).ok()
	}

	/// Returns the length of the encoded `T`.
	pub fn encoded_len(&self) -> usize {
		self.data.len()
	}

	/// Returns the encoded data.
	pub fn encoded(&self) -> &[u8] {
		&self.data
	}

	/// Create from the given encoded `data`.
	pub fn from_encoded(data: Vec<u8>) -> Self {
		Self { data, _phantom: sp_std::marker::PhantomData }
	}
}

impl<T: Encode> EncodeLike for WrapperKeepOpaque<T> {}
impl<T: Encode> EncodeLike<WrapperOpaque<T>> for WrapperKeepOpaque<T> {}

impl<T: Encode> Encode for WrapperKeepOpaque<T> {
	fn size_hint(&self) -> usize {
		self.data.len() + codec::Compact::<u32>::compact_len(&(self.data.len() as u32))
	}

	fn encode_to<O: codec::Output + ?Sized>(&self, dest: &mut O) {
		self.data.encode_to(dest);
	}

	fn encode(&self) -> Vec<u8> {
		self.data.encode()
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.data.using_encoded(f)
	}
}

impl<T: Decode> Decode for WrapperKeepOpaque<T> {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		Ok(Self { data: Vec::<u8>::decode(input)?, _phantom: sp_std::marker::PhantomData })
	}

	fn skip<I: Input>(input: &mut I) -> Result<(), codec::Error> {
		<Vec<u8>>::skip(input)
	}
}

impl<T: MaxEncodedLen> MaxEncodedLen for WrapperKeepOpaque<T> {
	fn max_encoded_len() -> usize {
		WrapperOpaque::<T>::max_encoded_len()
	}
}

impl<T: TypeInfo + 'static> TypeInfo for WrapperKeepOpaque<T> {
	type Identity = Self;
	fn type_info() -> Type {
		Type::builder()
			.path(Path::new("WrapperKeepOpaque", module_path!()))
			.type_params(vec![TypeParameter::new("T", Some(meta_type::<T>()))])
			.composite(
				Fields::unnamed()
					.field(|f| f.compact::<u32>())
					.field(|f| f.ty::<T>().type_name("T")),
			)
	}
}

/// A interface for looking up preimages from their hash on chain.
pub trait PreimageProvider<Hash> {
	/// Returns whether a preimage exists for a given hash.
	///
	/// A value of `true` implies that `get_preimage` is `Some`.
	fn have_preimage(hash: &Hash) -> bool;

	/// Returns the preimage for a given hash.
	fn get_preimage(hash: &Hash) -> Option<Vec<u8>>;

	/// Returns whether a preimage request exists for a given hash.
	fn preimage_requested(hash: &Hash) -> bool;

	/// Request that someone report a preimage. Providers use this to optimise the economics for
	/// preimage reporting.
	fn request_preimage(hash: &Hash);

	/// Cancel a previous preimage request.
	fn unrequest_preimage(hash: &Hash);
}

impl<Hash> PreimageProvider<Hash> for () {
	fn have_preimage(_: &Hash) -> bool {
		false
	}
	fn get_preimage(_: &Hash) -> Option<Vec<u8>> {
		None
	}
	fn preimage_requested(_: &Hash) -> bool {
		false
	}
	fn request_preimage(_: &Hash) {}
	fn unrequest_preimage(_: &Hash) {}
}

/// A interface for managing preimages to hashes on chain.
///
/// Note that this API does not assume any underlying user is calling, and thus
/// does not handle any preimage ownership or fees. Other system level logic that
/// uses this API should implement that on their own side.
pub trait PreimageRecipient<Hash>: PreimageProvider<Hash> {
	/// Maximum size of a preimage.
	type MaxSize: Get<u32>;

	/// Store the bytes of a preimage on chain infallible due to the bounded type.
	fn note_preimage(bytes: crate::BoundedVec<u8, Self::MaxSize>);

	/// Clear a previously noted preimage. This is infallible and should be treated more like a
	/// hint - if it was not previously noted or if it is now requested, then this will not do
	/// anything.
	fn unnote_preimage(hash: &Hash);
}

impl<Hash> PreimageRecipient<Hash> for () {
	type MaxSize = ();
	fn note_preimage(_: crate::BoundedVec<u8, Self::MaxSize>) {}
	fn unnote_preimage(_: &Hash) {}
}

/// Trait for creating an asset account with a deposit taken from a designated depositor specified
/// by the client.
pub trait AccountTouch<AssetId, AccountId> {
	/// The type for currency units of the deposit.
	type Balance;

	/// The deposit amount of a native currency required for creating an account of the `asset`.
	fn deposit_required(asset: AssetId) -> Self::Balance;

	/// Create an account for `who` of the `asset` with a deposit taken from the `depositor`.
	fn touch(asset: AssetId, who: AccountId, depositor: AccountId) -> DispatchResult;
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::bounded::{BoundedSlice, BoundedVec};
	use sp_std::marker::PhantomData;

	#[test]
	fn defensive_assert_works() {
		defensive_assert!(true);
		defensive_assert!(true,);
		defensive_assert!(true, "must work");
		defensive_assert!(true, "must work",);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive failure has been triggered!: \"1 == 0\": \"Must fail\"")]
	fn defensive_assert_panics() {
		defensive_assert!(1 == 0, "Must fail");
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_assert_does_not_panic() {
		defensive_assert!(1 == 0, "Must fail");
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_saturating_accrue_works() {
		let mut v = 1_u32;
		v.defensive_saturating_accrue(2);
		assert_eq!(v, 3);
		v.defensive_saturating_accrue(u32::MAX);
		assert_eq!(v, u32::MAX);
		v.defensive_saturating_accrue(1);
		assert_eq!(v, u32::MAX);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive")]
	fn defensive_saturating_accrue_panics() {
		let mut v = u32::MAX;
		v.defensive_saturating_accrue(1); // defensive failure
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_saturating_reduce_works() {
		let mut v = u32::MAX;
		v.defensive_saturating_reduce(3);
		assert_eq!(v, u32::MAX - 3);
		v.defensive_saturating_reduce(u32::MAX);
		assert_eq!(v, 0);
		v.defensive_saturating_reduce(1);
		assert_eq!(v, 0);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive")]
	fn defensive_saturating_reduce_panics() {
		let mut v = 0_u32;
		v.defensive_saturating_reduce(1); // defensive failure
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_saturating_inc_works() {
		let mut v = 0_u32;
		for i in 1..10 {
			v.defensive_saturating_inc();
			assert_eq!(v, i);
		}
		v += u32::MAX - 10;
		v.defensive_saturating_inc();
		assert_eq!(v, u32::MAX);
		v.defensive_saturating_inc();
		assert_eq!(v, u32::MAX);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive")]
	fn defensive_saturating_inc_panics() {
		let mut v = u32::MAX;
		v.defensive_saturating_inc(); // defensive failure
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_saturating_dec_works() {
		let mut v = u32::MAX;
		for i in 1..10 {
			v.defensive_saturating_dec();
			assert_eq!(v, u32::MAX - i);
		}
		v -= u32::MAX - 10;
		v.defensive_saturating_dec();
		assert_eq!(v, 0);
		v.defensive_saturating_dec();
		assert_eq!(v, 0);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive")]
	fn defensive_saturating_dec_panics() {
		let mut v = 0_u32;
		v.defensive_saturating_dec(); // defensive failure
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_truncating_from_vec_defensive_works() {
		let unbound = vec![1u32, 2];
		let bound = BoundedVec::<u32, ConstU32<1>>::defensive_truncate_from(unbound);
		assert_eq!(bound, vec![1u32]);
	}

	#[test]
	#[cfg(not(debug_assertions))]
	fn defensive_truncating_from_slice_defensive_works() {
		let unbound = &[1u32, 2];
		let bound = BoundedSlice::<u32, ConstU32<1>>::defensive_truncate_from(unbound);
		assert_eq!(bound, &[1u32][..]);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(
		expected = "Defensive failure has been triggered!: \"DefensiveTruncateFrom truncating\""
	)]
	fn defensive_truncating_from_vec_defensive_panics() {
		let unbound = vec![1u32, 2];
		let _ = BoundedVec::<u32, ConstU32<1>>::defensive_truncate_from(unbound);
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(
		expected = "Defensive failure has been triggered!: \"DefensiveTruncateFrom truncating\""
	)]
	fn defensive_truncating_from_slice_defensive_panics() {
		let unbound = &[1u32, 2];
		let _ = BoundedSlice::<u32, ConstU32<1>>::defensive_truncate_from(unbound);
	}

	#[test]
	fn defensive_truncate_from_vec_works() {
		let unbound = vec![1u32, 2, 3];
		let bound = BoundedVec::<u32, ConstU32<3>>::defensive_truncate_from(unbound.clone());
		assert_eq!(bound, unbound);
	}

	#[test]
	fn defensive_truncate_from_slice_works() {
		let unbound = [1u32, 2, 3];
		let bound = BoundedSlice::<u32, ConstU32<3>>::defensive_truncate_from(&unbound);
		assert_eq!(bound, &unbound[..]);
	}

	#[derive(Encode, Decode)]
	enum NestedType {
		Nested(Box<Self>),
		Done,
	}

	#[test]
	fn test_opaque_wrapper_decode_limit() {
		let limit = sp_api::MAX_EXTRINSIC_DEPTH as usize;
		let mut ok_bytes = vec![0u8; limit];
		ok_bytes.push(1u8);
		let mut err_bytes = vec![0u8; limit + 1];
		err_bytes.push(1u8);
		assert!(<WrapperOpaque<NestedType>>::decode(&mut &ok_bytes.encode()[..]).is_ok());
		assert!(<WrapperOpaque<NestedType>>::decode(&mut &err_bytes.encode()[..]).is_err());

		let ok_keep_opaque = WrapperKeepOpaque { data: ok_bytes, _phantom: PhantomData };
		let err_keep_opaque = WrapperKeepOpaque { data: err_bytes, _phantom: PhantomData };

		assert!(<WrapperKeepOpaque<NestedType>>::try_decode(&ok_keep_opaque).is_some());
		assert!(<WrapperKeepOpaque<NestedType>>::try_decode(&err_keep_opaque).is_none());
	}

	#[test]
	fn test_opaque_wrapper() {
		let encoded = WrapperOpaque(3u32).encode();
		assert_eq!(encoded, [codec::Compact(4u32).encode(), 3u32.to_le_bytes().to_vec()].concat());
		let vec_u8 = <Vec<u8>>::decode(&mut &encoded[..]).unwrap();
		let decoded_from_vec_u8 = u32::decode(&mut &vec_u8[..]).unwrap();
		assert_eq!(decoded_from_vec_u8, 3u32);
		let decoded = <WrapperOpaque<u32>>::decode(&mut &encoded[..]).unwrap();
		assert_eq!(decoded.0, 3u32);

		assert_eq!(<WrapperOpaque<[u8; 63]>>::max_encoded_len(), 63 + 1);
		assert_eq!(
			<WrapperOpaque<[u8; 63]>>::max_encoded_len(),
			WrapperOpaque([0u8; 63]).encode().len()
		);

		assert_eq!(<WrapperOpaque<[u8; 64]>>::max_encoded_len(), 64 + 2);
		assert_eq!(
			<WrapperOpaque<[u8; 64]>>::max_encoded_len(),
			WrapperOpaque([0u8; 64]).encode().len()
		);

		assert_eq!(
			<WrapperOpaque<[u8; 2usize.pow(14) - 1]>>::max_encoded_len(),
			2usize.pow(14) - 1 + 2
		);
		assert_eq!(<WrapperOpaque<[u8; 2usize.pow(14)]>>::max_encoded_len(), 2usize.pow(14) + 4);

		let data = 4u64;
		// Ensure that we check that the `Vec<u8>` is consumed completly on decode.
		assert!(WrapperOpaque::<u32>::decode(&mut &data.encode().encode()[..]).is_err());
	}

	#[test]
	fn test_keep_opaque_wrapper() {
		let data = 3u32.encode().encode();

		let keep_opaque = WrapperKeepOpaque::<u32>::decode(&mut &data[..]).unwrap();
		keep_opaque.try_decode().unwrap();

		let data = WrapperOpaque(50u32).encode();
		let decoded = WrapperKeepOpaque::<u32>::decode(&mut &data[..]).unwrap();
		let data = decoded.encode();
		WrapperOpaque::<u32>::decode(&mut &data[..]).unwrap();
	}

	#[test]
	fn defensive_min_works() {
		assert_eq!(10, 10_u32.defensive_min(11_u32));
		assert_eq!(10, 10_u32.defensive_min(10_u32));
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive failure has been triggered!: \"DefensiveMin\"")]
	fn defensive_min_panics() {
		10_u32.defensive_min(9_u32);
	}

	#[test]
	fn defensive_strict_min_works() {
		assert_eq!(10, 10_u32.defensive_strict_min(11_u32));
		assert_eq!(9, 9_u32.defensive_strict_min(10_u32));
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive failure has been triggered!: \"DefensiveMin strict\"")]
	fn defensive_strict_min_panics() {
		9_u32.defensive_strict_min(9_u32);
	}

	#[test]
	fn defensive_max_works() {
		assert_eq!(11, 11_u32.defensive_max(10_u32));
		assert_eq!(10, 10_u32.defensive_max(10_u32));
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive failure has been triggered!: \"DefensiveMax\"")]
	fn defensive_max_panics() {
		9_u32.defensive_max(10_u32);
	}

	#[test]
	fn defensive_strict_max_works() {
		assert_eq!(11, 11_u32.defensive_strict_max(10_u32));
		assert_eq!(10, 10_u32.defensive_strict_max(9_u32));
	}

	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "Defensive failure has been triggered!: \"DefensiveMax strict\"")]
	fn defensive_strict_max_panics() {
		9_u32.defensive_strict_max(9_u32);
	}
}
