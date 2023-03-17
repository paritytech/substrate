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

//! Minimal fixed point arithmetic primitives and types for runtime.

#![cfg_attr(not(feature = "std"), no_std)]

/// Copied from `sp-runtime` and documented there.
#[macro_export]
macro_rules! assert_eq_error_rate {
	($x:expr, $y:expr, $error:expr $(,)?) => {
		assert!(
			($x) >= (($y) - ($error)) && ($x) <= (($y) + ($error)),
			"{:?} != {:?} (with error rate {:?})",
			$x,
			$y,
			$error,
		);
	};
}

pub mod biguint;
pub mod fixed_point;
pub mod helpers_128bit;
pub mod per_things;
pub mod rational;
pub mod traits;

pub use fixed_point::{FixedI128, FixedI64, FixedPointNumber, FixedPointOperand, FixedU128};
pub use per_things::{
	InnerOf, MultiplyArg, PerThing, PerU16, Perbill, Percent, Permill, Perquintill, RationalArg,
	ReciprocalArg, Rounding, SignedRounding, UpperOf,
};
pub use rational::{Rational128, RationalInfinite};

use sp_std::{cmp::Ordering, fmt::Debug, prelude::*};
use traits::{BaseArithmetic, One, SaturatedConversion, Unsigned, Zero};

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

/// Arithmetic errors.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum ArithmeticError {
	/// Underflow.
	Underflow,
	/// Overflow.
	Overflow,
	/// Division by zero.
	DivisionByZero,
}

impl From<ArithmeticError> for &'static str {
	fn from(e: ArithmeticError) -> &'static str {
		match e {
			ArithmeticError::Underflow => "An underflow would occur",
			ArithmeticError::Overflow => "An overflow would occur",
			ArithmeticError::DivisionByZero => "Division by zero",
		}
	}
}

/// Trait for comparing two numbers with an threshold.
///
/// Returns:
/// - `Ordering::Greater` if `self` is greater than `other + threshold`.
/// - `Ordering::Less` if `self` is less than `other - threshold`.
/// - `Ordering::Equal` otherwise.
pub trait ThresholdOrd<T> {
	/// Compare if `self` is `threshold` greater or less than `other`.
	fn tcmp(&self, other: &T, threshold: T) -> Ordering;
}

impl<T> ThresholdOrd<T> for T
where
	T: Ord + PartialOrd + Copy + Clone + traits::Zero + traits::Saturating,
{
	fn tcmp(&self, other: &T, threshold: T) -> Ordering {
		// early exit.
		if threshold.is_zero() {
			return self.cmp(other)
		}

		let upper_bound = other.saturating_add(threshold);
		let lower_bound = other.saturating_sub(threshold);

		if upper_bound <= lower_bound {
			// defensive only. Can never happen.
			self.cmp(other)
		} else {
			// upper_bound is guaranteed now to be bigger than lower.
			match (self.cmp(&lower_bound), self.cmp(&upper_bound)) {
				(Ordering::Greater, Ordering::Greater) => Ordering::Greater,
				(Ordering::Less, Ordering::Less) => Ordering::Less,
				_ => Ordering::Equal,
			}
		}
	}
}

/// A collection-like object that is made of values of type `T` and can normalize its individual
/// values around a centric point.
///
/// Note that the order of items in the collection may affect the result.
pub trait Normalizable<T> {
	/// Normalize self around `targeted_sum`.
	///
	/// Only returns `Ok` if the new sum of results is guaranteed to be equal to `targeted_sum`.
	/// Else, returns an error explaining why it failed to do so.
	fn normalize(&self, targeted_sum: T) -> Result<Vec<T>, &'static str>;
}

macro_rules! impl_normalize_for_numeric {
	($($numeric:ty),*) => {
		$(
			impl Normalizable<$numeric> for Vec<$numeric> {
				fn normalize(&self, targeted_sum: $numeric) -> Result<Vec<$numeric>, &'static str> {
					normalize(self.as_ref(), targeted_sum)
				}
			}
		)*
	};
}

impl_normalize_for_numeric!(u8, u16, u32, u64, u128);

impl<P: PerThing> Normalizable<P> for Vec<P> {
	fn normalize(&self, targeted_sum: P) -> Result<Vec<P>, &'static str> {
		let uppers = self.iter().map(|p| <UpperOf<P>>::from(p.deconstruct())).collect::<Vec<_>>();

		let normalized =
			normalize(uppers.as_ref(), <UpperOf<P>>::from(targeted_sum.deconstruct()))?;

		Ok(normalized
			.into_iter()
			.map(|i: UpperOf<P>| P::from_parts(i.saturated_into::<P::Inner>()))
			.collect())
	}
}

/// Normalize `input` so that the sum of all elements reaches `targeted_sum`.
///
/// This implementation is currently in a balanced position between being performant and accurate.
///
/// 1. We prefer storing original indices, and sorting the `input` only once. This will save the
///    cost of sorting per round at the cost of a little bit of memory.
/// 2. The granularity of increment/decrements is determined by the number of elements in `input`
///    and their sum difference with `targeted_sum`, namely `diff = diff(sum(input), target_sum)`.
///    This value is then distributed into `per_round = diff / input.len()` and `leftover = diff %
///    round`. First, per_round is applied to all elements of input, and then we move to leftover,
///    in which case we add/subtract 1 by 1 until `leftover` is depleted.
///
/// When the sum is less than the target, the above approach always holds. In this case, then each
/// individual element is also less than target. Thus, by adding `per_round` to each item, neither
/// of them can overflow the numeric bound of `T`. In fact, neither of the can go beyond
/// `target_sum`*.
///
/// If sum is more than target, there is small twist. The subtraction of `per_round`
/// form each element might go below zero. In this case, we saturate and add the error to the
/// `leftover` value. This ensures that the result will always stay accurate, yet it might cause the
/// execution to become increasingly slow, since leftovers are applied one by one.
///
/// All in all, the complicated case above is rare to happen in most use cases within this repo ,
/// hence we opt for it due to its simplicity.
///
/// This function will return an error is if length of `input` cannot fit in `T`, or if `sum(input)`
/// cannot fit inside `T`.
///
/// * This proof is used in the implementation as well.
pub fn normalize<T>(input: &[T], targeted_sum: T) -> Result<Vec<T>, &'static str>
where
	T: Clone + Copy + Ord + BaseArithmetic + Unsigned + Debug,
{
	// compute sum and return error if failed.
	let mut sum = T::zero();
	for t in input.iter() {
		sum = sum.checked_add(t).ok_or("sum of input cannot fit in `T`")?;
	}

	// convert count and return error if failed.
	let count = input.len();
	let count_t: T = count.try_into().map_err(|_| "length of `inputs` cannot fit in `T`")?;

	// Nothing to do here.
	if count.is_zero() {
		return Ok(Vec::<T>::new())
	}

	let diff = targeted_sum.max(sum) - targeted_sum.min(sum);
	if diff.is_zero() {
		return Ok(input.to_vec())
	}

	let needs_bump = targeted_sum > sum;
	let per_round = diff / count_t;
	let mut leftover = diff % count_t;

	// sort output once based on diff. This will require more data transfer and saving original
	// index, but we sort only twice instead: once now and once at the very end.
	let mut output_with_idx = input.iter().cloned().enumerate().collect::<Vec<(usize, T)>>();
	output_with_idx.sort_by_key(|x| x.1);

	if needs_bump {
		// must increase the values a bit. Bump from the min element. Index of minimum is now zero
		// because we did a sort. If at any point the min goes greater or equal the `max_threshold`,
		// we move to the next minimum.
		let mut min_index = 0;
		// at this threshold we move to next index.
		let threshold = targeted_sum / count_t;

		if !per_round.is_zero() {
			for _ in 0..count {
				output_with_idx[min_index].1 = output_with_idx[min_index]
					.1
					.checked_add(&per_round)
					.expect("Proof provided in the module doc; qed.");
				if output_with_idx[min_index].1 >= threshold {
					min_index += 1;
					min_index %= count;
				}
			}
		}

		// continue with the previous min_index
		while !leftover.is_zero() {
			output_with_idx[min_index].1 = output_with_idx[min_index]
				.1
				.checked_add(&T::one())
				.expect("Proof provided in the module doc; qed.");
			if output_with_idx[min_index].1 >= threshold {
				min_index += 1;
				min_index %= count;
			}
			leftover -= One::one()
		}
	} else {
		// must decrease the stakes a bit. decrement from the max element. index of maximum is now
		// last. if at any point the max goes less or equal the `min_threshold`, we move to the next
		// maximum.
		let mut max_index = count - 1;
		// at this threshold we move to next index.
		let threshold = output_with_idx
			.first()
			.expect("length of input is greater than zero; it must have a first; qed")
			.1;

		if !per_round.is_zero() {
			for _ in 0..count {
				output_with_idx[max_index].1 =
					output_with_idx[max_index].1.checked_sub(&per_round).unwrap_or_else(|| {
						let remainder = per_round - output_with_idx[max_index].1;
						leftover += remainder;
						output_with_idx[max_index].1.saturating_sub(per_round)
					});
				if output_with_idx[max_index].1 <= threshold {
					max_index = max_index.checked_sub(1).unwrap_or(count - 1);
				}
			}
		}

		// continue with the previous max_index
		while !leftover.is_zero() {
			if let Some(next) = output_with_idx[max_index].1.checked_sub(&One::one()) {
				output_with_idx[max_index].1 = next;
				if output_with_idx[max_index].1 <= threshold {
					max_index = max_index.checked_sub(1).unwrap_or(count - 1);
				}
				leftover -= One::one()
			} else {
				max_index = max_index.checked_sub(1).unwrap_or(count - 1);
			}
		}
	}

	debug_assert_eq!(
		output_with_idx.iter().fold(T::zero(), |acc, (_, x)| acc + *x),
		targeted_sum,
		"sum({:?}) != {:?}",
		output_with_idx,
		targeted_sum,
	);

	// sort again based on the original index.
	output_with_idx.sort_by_key(|x| x.0);
	Ok(output_with_idx.into_iter().map(|(_, t)| t).collect())
}

#[cfg(test)]
mod normalize_tests {
	use super::*;

	#[test]
	fn work_for_all_types() {
		macro_rules! test_for {
			($type:ty) => {
				assert_eq!(
					normalize(vec![8 as $type, 9, 7, 10].as_ref(), 40).unwrap(),
					vec![10, 10, 10, 10],
				);
			};
		}
		// it should work for all types as long as the length of vector can be converted to T.
		test_for!(u128);
		test_for!(u64);
		test_for!(u32);
		test_for!(u16);
		test_for!(u8);
	}

	#[test]
	fn fails_on_if_input_sum_large() {
		assert!(normalize(vec![1u8; 255].as_ref(), 10).is_ok());
		assert_eq!(normalize(vec![1u8; 256].as_ref(), 10), Err("sum of input cannot fit in `T`"));
	}

	#[test]
	fn does_not_fail_on_subtraction_overflow() {
		assert_eq!(normalize(vec![1u8, 100, 100].as_ref(), 10).unwrap(), vec![1, 9, 0]);
		assert_eq!(normalize(vec![1u8, 8, 9].as_ref(), 1).unwrap(), vec![0, 1, 0]);
	}

	#[test]
	fn works_for_vec() {
		assert_eq!(vec![8u32, 9, 7, 10].normalize(40).unwrap(), vec![10u32, 10, 10, 10]);
	}

	#[test]
	fn works_for_per_thing() {
		assert_eq!(
			vec![Perbill::from_percent(33), Perbill::from_percent(33), Perbill::from_percent(33)]
				.normalize(Perbill::one())
				.unwrap(),
			vec![
				Perbill::from_parts(333333334),
				Perbill::from_parts(333333333),
				Perbill::from_parts(333333333),
			]
		);

		assert_eq!(
			vec![Perbill::from_percent(20), Perbill::from_percent(15), Perbill::from_percent(30)]
				.normalize(Perbill::one())
				.unwrap(),
			vec![
				Perbill::from_parts(316666668),
				Perbill::from_parts(383333332),
				Perbill::from_parts(300000000),
			]
		);
	}

	#[test]
	fn can_work_for_peru16() {
		// Peru16 is a rather special case; since inner type is exactly the same as capacity, we
		// could have a situation where the sum cannot be calculated in the inner type. Calculating
		// using the upper type of the per_thing should assure this to be okay.
		assert_eq!(
			vec![PerU16::from_percent(40), PerU16::from_percent(40), PerU16::from_percent(40),]
				.normalize(PerU16::one())
				.unwrap(),
			vec![
				PerU16::from_parts(21845), // 33%
				PerU16::from_parts(21845), // 33%
				PerU16::from_parts(21845), // 33%
			]
		);
	}

	#[test]
	fn normalize_works_all_le() {
		assert_eq!(normalize(vec![8u32, 9, 7, 10].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);

		assert_eq!(normalize(vec![7u32, 7, 7, 7].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);

		assert_eq!(normalize(vec![7u32, 7, 7, 10].as_ref(), 40).unwrap(), vec![11, 11, 8, 10]);

		assert_eq!(normalize(vec![7u32, 8, 7, 10].as_ref(), 40).unwrap(), vec![11, 8, 11, 10]);

		assert_eq!(normalize(vec![7u32, 7, 8, 10].as_ref(), 40).unwrap(), vec![11, 11, 8, 10]);
	}

	#[test]
	fn normalize_works_some_ge() {
		assert_eq!(normalize(vec![8u32, 11, 9, 10].as_ref(), 40).unwrap(), vec![10, 11, 9, 10]);
	}

	#[test]
	fn always_inc_min() {
		assert_eq!(normalize(vec![10u32, 7, 10, 10].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);
		assert_eq!(normalize(vec![10u32, 10, 7, 10].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);
		assert_eq!(normalize(vec![10u32, 10, 10, 7].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);
	}

	#[test]
	fn normalize_works_all_ge() {
		assert_eq!(normalize(vec![12u32, 11, 13, 10].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);

		assert_eq!(normalize(vec![13u32, 13, 13, 13].as_ref(), 40).unwrap(), vec![10, 10, 10, 10]);

		assert_eq!(normalize(vec![13u32, 13, 13, 10].as_ref(), 40).unwrap(), vec![12, 9, 9, 10]);

		assert_eq!(normalize(vec![13u32, 12, 13, 10].as_ref(), 40).unwrap(), vec![9, 12, 9, 10]);

		assert_eq!(normalize(vec![13u32, 13, 12, 10].as_ref(), 40).unwrap(), vec![9, 9, 12, 10]);
	}
}

#[cfg(test)]
mod threshold_compare_tests {
	use super::*;
	use crate::traits::Saturating;
	use sp_std::cmp::Ordering;

	#[test]
	fn epsilon_ord_works() {
		let b = 115u32;
		let e = Perbill::from_percent(10).mul_ceil(b);

		// [115 - 11,5 (103,5), 115 + 11,5 (126,5)] is all equal
		assert_eq!(103u32.tcmp(&b, e), Ordering::Equal);
		assert_eq!(104u32.tcmp(&b, e), Ordering::Equal);
		assert_eq!(115u32.tcmp(&b, e), Ordering::Equal);
		assert_eq!(120u32.tcmp(&b, e), Ordering::Equal);
		assert_eq!(126u32.tcmp(&b, e), Ordering::Equal);
		assert_eq!(127u32.tcmp(&b, e), Ordering::Equal);

		assert_eq!(128u32.tcmp(&b, e), Ordering::Greater);
		assert_eq!(102u32.tcmp(&b, e), Ordering::Less);
	}

	#[test]
	fn epsilon_ord_works_with_small_epc() {
		let b = 115u32;
		// way less than 1 percent. threshold will be zero. Result should be same as normal ord.
		let e = Perbill::from_parts(100) * b;

		// [115 - 11,5 (103,5), 115 + 11,5 (126,5)] is all equal
		assert_eq!(103u32.tcmp(&b, e), 103u32.cmp(&b));
		assert_eq!(104u32.tcmp(&b, e), 104u32.cmp(&b));
		assert_eq!(115u32.tcmp(&b, e), 115u32.cmp(&b));
		assert_eq!(120u32.tcmp(&b, e), 120u32.cmp(&b));
		assert_eq!(126u32.tcmp(&b, e), 126u32.cmp(&b));
		assert_eq!(127u32.tcmp(&b, e), 127u32.cmp(&b));

		assert_eq!(128u32.tcmp(&b, e), 128u32.cmp(&b));
		assert_eq!(102u32.tcmp(&b, e), 102u32.cmp(&b));
	}

	#[test]
	fn peru16_rational_does_not_overflow() {
		// A historical example that will panic only for per_thing type that are created with
		// maximum capacity of their type, e.g. PerU16.
		let _ = PerU16::from_rational(17424870u32, 17424870);
	}

	#[test]
	fn saturating_mul_works() {
		assert_eq!(Saturating::saturating_mul(2, i32::MIN), i32::MIN);
		assert_eq!(Saturating::saturating_mul(2, i32::MAX), i32::MAX);
	}

	#[test]
	fn saturating_pow_works() {
		assert_eq!(Saturating::saturating_pow(i32::MIN, 0), 1);
		assert_eq!(Saturating::saturating_pow(i32::MAX, 0), 1);
		assert_eq!(Saturating::saturating_pow(i32::MIN, 3), i32::MIN);
		assert_eq!(Saturating::saturating_pow(i32::MIN, 2), i32::MAX);
		assert_eq!(Saturating::saturating_pow(i32::MAX, 2), i32::MAX);
	}
}
