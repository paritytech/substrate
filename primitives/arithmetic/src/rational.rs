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

use crate::{biguint::BigUint, helpers_128bit};
use num_traits::{Bounded, One, Zero};
use sp_std::{cmp::Ordering, prelude::*};

/// A wrapper for any rational number with infinitely large numerator and denominator.
///
/// This type exists to facilitate `cmp` operation
/// on values like `a/b < c/d` where `a, b, c, d` are all `BigUint`.
#[derive(Clone, Default, Eq)]
pub struct RationalInfinite(BigUint, BigUint);

impl RationalInfinite {
	/// Return the numerator reference.
	pub fn n(&self) -> &BigUint {
		&self.0
	}

	/// Return the denominator reference.
	pub fn d(&self) -> &BigUint {
		&self.1
	}

	/// Build from a raw `n/d`.
	pub fn from(n: BigUint, d: BigUint) -> Self {
		Self(n, d.max(BigUint::one()))
	}

	/// Zero.
	pub fn zero() -> Self {
		Self(BigUint::zero(), BigUint::one())
	}

	/// One.
	pub fn one() -> Self {
		Self(BigUint::one(), BigUint::one())
	}
}

impl PartialOrd for RationalInfinite {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for RationalInfinite {
	fn cmp(&self, other: &Self) -> Ordering {
		// handle some edge cases.
		if self.d() == other.d() {
			self.n().cmp(other.n())
		} else if self.d().is_zero() {
			Ordering::Greater
		} else if other.d().is_zero() {
			Ordering::Less
		} else {
			// (a/b) cmp (c/d) => (a*d) cmp (c*b)
			self.n().clone().mul(other.d()).cmp(&other.n().clone().mul(self.d()))
		}
	}
}

impl PartialEq for RationalInfinite {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == Ordering::Equal
	}
}

impl From<Rational128> for RationalInfinite {
	fn from(t: Rational128) -> Self {
		Self(t.0.into(), t.1.into())
	}
}

/// A wrapper for any rational number with a 128 bit numerator and denominator.
#[derive(Clone, Copy, Default, Eq)]
pub struct Rational128(u128, u128);

#[cfg(feature = "std")]
impl sp_std::fmt::Debug for Rational128 {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "Rational128({:.4})", self.0 as f32 / self.1 as f32)
	}
}

#[cfg(not(feature = "std"))]
impl sp_std::fmt::Debug for Rational128 {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "Rational128(..)")
	}
}

impl Rational128 {
	/// Zero.
	pub fn zero() -> Self {
		Self(0, 1)
	}

	/// One
	pub fn one() -> Self {
		Self(1, 1)
	}

	/// If it is zero or not
	pub fn is_zero(&self) -> bool {
		self.0.is_zero()
	}

	/// Build from a raw `n/d`.
	pub fn from(n: u128, d: u128) -> Self {
		Self(n, d.max(1))
	}

	/// Build from a raw `n/d`. This could lead to / 0 if not properly handled.
	pub fn from_unchecked(n: u128, d: u128) -> Self {
		Self(n, d)
	}

	/// Return the numerator.
	pub fn n(&self) -> u128 {
		self.0
	}

	/// Return the denominator.
	pub fn d(&self) -> u128 {
		self.1
	}

	/// Convert `self` to a similar rational number where denominator is the given `den`.
	//
	/// This only returns if the result is accurate. `Err` is returned if the result cannot be
	/// accurately calculated.
	pub fn to_den(self, den: u128) -> Result<Self, &'static str> {
		if den == self.1 {
			Ok(self)
		} else {
			helpers_128bit::multiply_by_rational(self.0, den, self.1).map(|n| Self(n, den))
		}
	}

	/// Get the least common divisor of `self` and `other`.
	///
	/// This only returns if the result is accurate. `Err` is returned if the result cannot be
	/// accurately calculated.
	pub fn lcm(&self, other: &Self) -> Result<u128, &'static str> {
		// this should be tested better: two large numbers that are almost the same.
		if self.1 == other.1 {
			return Ok(self.1)
		}
		let g = helpers_128bit::gcd(self.1, other.1);
		helpers_128bit::multiply_by_rational(self.1, other.1, g)
	}

	/// A saturating add that assumes `self` and `other` have the same denominator.
	pub fn lazy_saturating_add(self, other: Self) -> Self {
		if other.is_zero() {
			self
		} else {
			Self(self.0.saturating_add(other.0), self.1)
		}
	}

	/// A saturating subtraction that assumes `self` and `other` have the same denominator.
	pub fn lazy_saturating_sub(self, other: Self) -> Self {
		if other.is_zero() {
			self
		} else {
			Self(self.0.saturating_sub(other.0), self.1)
		}
	}

	/// Addition. Simply tries to unify the denominators and add the numerators.
	///
	/// Overflow might happen during any of the steps. Error is returned in such cases.
	pub fn checked_add(self, other: Self) -> Result<Self, &'static str> {
		let lcm = self.lcm(&other).map_err(|_| "failed to scale to denominator")?;
		let self_scaled = self.to_den(lcm).map_err(|_| "failed to scale to denominator")?;
		let other_scaled = other.to_den(lcm).map_err(|_| "failed to scale to denominator")?;
		let n = self_scaled
			.0
			.checked_add(other_scaled.0)
			.ok_or("overflow while adding numerators")?;
		Ok(Self(n, self_scaled.1))
	}

	/// Subtraction. Simply tries to unify the denominators and subtract the numerators.
	///
	/// Overflow might happen during any of the steps. None is returned in such cases.
	pub fn checked_sub(self, other: Self) -> Result<Self, &'static str> {
		let lcm = self.lcm(&other).map_err(|_| "failed to scale to denominator")?;
		let self_scaled = self.to_den(lcm).map_err(|_| "failed to scale to denominator")?;
		let other_scaled = other.to_den(lcm).map_err(|_| "failed to scale to denominator")?;

		let n = self_scaled
			.0
			.checked_sub(other_scaled.0)
			.ok_or("overflow while subtracting numerators")?;
		Ok(Self(n, self_scaled.1))
	}
}

impl Bounded for Rational128 {
	fn min_value() -> Self {
		Self(0, 1)
	}

	fn max_value() -> Self {
		Self(Bounded::max_value(), 1)
	}
}

impl<T: Into<u128>> From<T> for Rational128 {
	fn from(t: T) -> Self {
		Self::from(t.into(), 1)
	}
}

impl PartialOrd for Rational128 {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for Rational128 {
	fn cmp(&self, other: &Self) -> Ordering {
		// handle some edge cases.
		if self.1 == other.1 {
			self.0.cmp(&other.0)
		} else if self.1.is_zero() {
			Ordering::Greater
		} else if other.1.is_zero() {
			Ordering::Less
		} else {
			// Don't even compute gcd.
			let self_n = helpers_128bit::to_big_uint(self.0) * helpers_128bit::to_big_uint(other.1);
			let other_n =
				helpers_128bit::to_big_uint(other.0) * helpers_128bit::to_big_uint(self.1);
			self_n.cmp(&other_n)
		}
	}
}

impl PartialEq for Rational128 {
	fn eq(&self, other: &Self) -> bool {
		// handle some edge cases.
		if self.1 == other.1 {
			self.0.eq(&other.0)
		} else {
			let self_n = helpers_128bit::to_big_uint(self.0) * helpers_128bit::to_big_uint(other.1);
			let other_n =
				helpers_128bit::to_big_uint(other.0) * helpers_128bit::to_big_uint(self.1);
			self_n.eq(&other_n)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{helpers_128bit::*, *};
	use static_assertions::const_assert;

	const MAX128: u128 = u128::MAX;
	const MAX64: u128 = u64::MAX as u128;
	const MAX64_2: u128 = 2 * u64::MAX as u128;

	fn r(p: u128, q: u128) -> Rational128 {
		Rational128(p, q)
	}

	fn mul_div(a: u128, b: u128, c: u128) -> u128 {
		use primitive_types::U256;
		if a.is_zero() {
			return Zero::zero()
		}
		let c = c.max(1);

		// e for extended
		let ae: U256 = a.into();
		let be: U256 = b.into();
		let ce: U256 = c.into();

		let r = ae * be / ce;
		if r > u128::max_value().into() {
			a
		} else {
			r.as_u128()
		}
	}

	#[test]
	fn truth_value_function_works() {
		assert_eq!(mul_div(2u128.pow(100), 8, 4), 2u128.pow(101));
		assert_eq!(mul_div(2u128.pow(100), 4, 8), 2u128.pow(99));

		// and it returns a if result cannot fit
		assert_eq!(mul_div(MAX128 - 10, 2, 1), MAX128 - 10);
	}

	#[test]
	fn to_denom_works() {
		// simple up and down
		assert_eq!(r(1, 5).to_den(10), Ok(r(2, 10)));
		assert_eq!(r(4, 10).to_den(5), Ok(r(2, 5)));

		// up and down with large numbers
		assert_eq!(r(MAX128 - 10, MAX128).to_den(10), Ok(r(10, 10)));
		assert_eq!(r(MAX128 / 2, MAX128).to_den(10), Ok(r(5, 10)));

		// large to perbill. This is very well needed for npos-elections.
		assert_eq!(r(MAX128 / 2, MAX128).to_den(1000_000_000), Ok(r(500_000_000, 1000_000_000)));

		// large to large
		assert_eq!(r(MAX128 / 2, MAX128).to_den(MAX128 / 2), Ok(r(MAX128 / 4, MAX128 / 2)));
	}

	#[test]
	fn gdc_works() {
		assert_eq!(gcd(10, 5), 5);
		assert_eq!(gcd(7, 22), 1);
	}

	#[test]
	fn lcm_works() {
		// simple stuff
		assert_eq!(r(3, 10).lcm(&r(4, 15)).unwrap(), 30);
		assert_eq!(r(5, 30).lcm(&r(1, 7)).unwrap(), 210);
		assert_eq!(r(5, 30).lcm(&r(1, 10)).unwrap(), 30);

		// large numbers
		assert_eq!(
			r(1_000_000_000, MAX128).lcm(&r(7_000_000_000, MAX128 - 1)),
			Err("result cannot fit in u128"),
		);
		assert_eq!(
			r(1_000_000_000, MAX64).lcm(&r(7_000_000_000, MAX64 - 1)),
			Ok(340282366920938463408034375210639556610),
		);
		const_assert!(340282366920938463408034375210639556610 < MAX128);
		const_assert!(340282366920938463408034375210639556610 == MAX64 * (MAX64 - 1));
	}

	#[test]
	fn add_works() {
		// works
		assert_eq!(r(3, 10).checked_add(r(1, 10)).unwrap(), r(2, 5));
		assert_eq!(r(3, 10).checked_add(r(3, 7)).unwrap(), r(51, 70));

		// errors
		assert_eq!(
			r(1, MAX128).checked_add(r(1, MAX128 - 1)),
			Err("failed to scale to denominator"),
		);
		assert_eq!(
			r(7, MAX128).checked_add(r(MAX128, MAX128)),
			Err("overflow while adding numerators"),
		);
		assert_eq!(
			r(MAX128, MAX128).checked_add(r(MAX128, MAX128)),
			Err("overflow while adding numerators"),
		);
	}

	#[test]
	fn sub_works() {
		// works
		assert_eq!(r(3, 10).checked_sub(r(1, 10)).unwrap(), r(1, 5));
		assert_eq!(r(6, 10).checked_sub(r(3, 7)).unwrap(), r(12, 70));

		// errors
		assert_eq!(
			r(2, MAX128).checked_sub(r(1, MAX128 - 1)),
			Err("failed to scale to denominator"),
		);
		assert_eq!(
			r(7, MAX128).checked_sub(r(MAX128, MAX128)),
			Err("overflow while subtracting numerators"),
		);
		assert_eq!(r(1, 10).checked_sub(r(2, 10)), Err("overflow while subtracting numerators"));
	}

	#[test]
	fn ordering_and_eq_works() {
		assert!(r(1, 2) > r(1, 3));
		assert!(r(1, 2) > r(2, 6));

		assert!(r(1, 2) < r(6, 6));
		assert!(r(2, 1) > r(2, 6));

		assert!(r(5, 10) == r(1, 2));
		assert!(r(1, 2) == r(1, 2));

		assert!(r(1, 1490000000000200000) > r(1, 1490000000000200001));
	}

	#[test]
	fn multiply_by_rational_works() {
		assert_eq!(multiply_by_rational(7, 2, 3).unwrap(), 7 * 2 / 3);
		assert_eq!(multiply_by_rational(7, 20, 30).unwrap(), 7 * 2 / 3);
		assert_eq!(multiply_by_rational(20, 7, 30).unwrap(), 7 * 2 / 3);

		assert_eq!(
			// MAX128 % 3 == 0
			multiply_by_rational(MAX128, 2, 3).unwrap(),
			MAX128 / 3 * 2,
		);
		assert_eq!(
			// MAX128 % 7 == 3
			multiply_by_rational(MAX128, 5, 7).unwrap(),
			(MAX128 / 7 * 5) + (3 * 5 / 7),
		);
		assert_eq!(
			// MAX128 % 7 == 3
			multiply_by_rational(MAX128, 11, 13).unwrap(),
			(MAX128 / 13 * 11) + (8 * 11 / 13),
		);
		assert_eq!(
			// MAX128 % 1000 == 455
			multiply_by_rational(MAX128, 555, 1000).unwrap(),
			(MAX128 / 1000 * 555) + (455 * 555 / 1000),
		);

		assert_eq!(multiply_by_rational(2 * MAX64 - 1, MAX64, MAX64).unwrap(), 2 * MAX64 - 1);
		assert_eq!(multiply_by_rational(2 * MAX64 - 1, MAX64 - 1, MAX64).unwrap(), 2 * MAX64 - 3);

		assert_eq!(
			multiply_by_rational(MAX64 + 100, MAX64_2, MAX64_2 / 2).unwrap(),
			(MAX64 + 100) * 2,
		);
		assert_eq!(
			multiply_by_rational(MAX64 + 100, MAX64_2 / 100, MAX64_2 / 200).unwrap(),
			(MAX64 + 100) * 2,
		);

		assert_eq!(
			multiply_by_rational(2u128.pow(66) - 1, 2u128.pow(65) - 1, 2u128.pow(65)).unwrap(),
			73786976294838206461,
		);
		assert_eq!(multiply_by_rational(1_000_000_000, MAX128 / 8, MAX128 / 2).unwrap(), 250000000);

		assert_eq!(
			multiply_by_rational(
				29459999999999999988000u128,
				1000000000000000000u128,
				10000000000000000000u128
			)
			.unwrap(),
			2945999999999999998800u128
		);
	}

	#[test]
	fn multiply_by_rational_a_b_are_interchangeable() {
		assert_eq!(multiply_by_rational(10, MAX128, MAX128 / 2), Ok(20));
		assert_eq!(multiply_by_rational(MAX128, 10, MAX128 / 2), Ok(20));
	}

	#[test]
	#[ignore]
	fn multiply_by_rational_fuzzed_equation() {
		assert_eq!(
			multiply_by_rational(154742576605164960401588224, 9223376310179529214, 549756068598),
			Ok(2596149632101417846585204209223679)
		);
	}
}
