// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use sp_std::{
	ops, prelude::*,
	convert::{TryFrom, TryInto},
};
use codec::{Encode, Decode};
use crate::{
	Perquintill,
	traits::{
		SaturatedConversion, CheckedSub, CheckedAdd, CheckedDiv, Bounded, UniqueSaturatedInto, Saturating
	},
	helpers_128bit::multiply_by_rational,
};

/// A signed fixed point number. Can hold any value in the range
/// [-170_141_183_460_469_231_731, 170_141_183_460_469_231_731]
/// with an additional fixed point accuracy of 18 decimal points.
/// i.e. 170000000000000000000.000000000000000001 can be represented by Fixed128.
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed128(i128);

/// The accuracy of the `Fixed128` type.
const DIV: i128 = 1_000_000_000_000_000_000;
const U_DIV: u128 = 1_000_000_000_000_000_000;

impl Fixed128 {
	/// creates self from a natural number.
	///
	/// Note that this might be lossy.
	pub fn from_natural(int: i128) -> Self {
		Self(int.saturating_mul(DIV))
	}

	/// Return the accuracy of the type. Given that this function returns the value `X`, it means
	/// that an instance composed of `X` parts (`Fixed128::from_parts(X)`) is equal to `1`.
	pub fn accuracy() -> i128 {
		DIV
	}

	/// Consume self and return the inner value.
	///
	/// This should only be used for testing.
	#[cfg(any(feature = "std", test))]
	pub fn into_inner(self) -> i128 { self.0 }

	/// Raw constructor. Equal to `parts / 1_000_000_000_000_000_000`.
	pub fn from_parts(parts: i128) -> Self {
		Self(parts)
	}

	/// creates self from a rational number. Equal to `n/d`.
	///
	/// Note that this might be lossy.
	pub fn from_rational(n: i128, d: u128) -> Self {
		// Turn n into a positive number, and track the original sign.
		// This lossy by 1 if n is exactly i128.min_value()
		let (n, sign): (u128, i128) = if n == i128::min_value() {
			(i128::max_value().try_into().expect("i128 max value can fit into u128"), -1)
		} else if n.is_negative() {
			((n * -1).try_into().expect("positive i128 can always fit into u128"), -1)
		} else {
			(n.try_into().expect("positive i128 can always fit into u128"), 1)
		};
		// This should never fail, but if it does, it is because value was too big for u128
		// so we map to u128 max value. TODO: Can we expect here that value is always smaller?
		let result = multiply_by_rational(n, U_DIV, d.max(1)).unwrap_or(u128::max_value());
		// If the u128 result wont fit in i128, we do i128 max. TODO: Can we expect value is always smaller?
		let signed_result: i128 = sign * result.try_into().unwrap_or(i128::max_value());
		Self(signed_result)
	}

	/// Performs a saturated multiply and accumulate by unsigned number.
	///
	/// Returns a saturated `int + (self * int)`.
	pub fn saturated_multiply_accumulate<N>(self, int: N) -> N
		where
			N: TryFrom<u128> + From<u64> + UniqueSaturatedInto<u64> + Bounded + Clone + Saturating +
			ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
			ops::Add<N, Output=N>,
	{
		let div = DIV as u128;
		let positive = self.0 > 0;
		// safe to convert as absolute value.
		let parts = self.0.checked_abs().map(|v| v as u128).unwrap_or(i128::max_value() as u128 + 1);


		// will always fit.
		let natural_parts = parts / div;
		// might saturate.
		let natural_parts: N = natural_parts.saturated_into();
		// fractional parts can always fit into u64.
		let perquintill_parts = (parts % div) as u64;

		let n = int.clone().saturating_mul(natural_parts);
		let p = Perquintill::from_parts(perquintill_parts) * int.clone();

		// everything that needs to be either added or subtracted from the original weight.
		let excess = n.saturating_add(p);

		if positive {
			int.saturating_add(excess)
		} else {
			int.saturating_sub(excess)
		}
	}
}

impl Saturating for Fixed128 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		Self(self.0.saturating_mul(rhs.0) / DIV)
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self(self.0.saturating_pow(exp as u32))
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe addition.
impl ops::Add for Fixed128 {
	type Output = Self;

	fn add(self, rhs: Self) -> Self::Output {
		Self(self.0 + rhs.0)
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe subtraction.
impl ops::Sub for Fixed128 {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		Self(self.0 - rhs.0)
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `CheckedDiv` trait
/// for safe division.
impl ops::Div for Fixed128 {
	type Output = Self;

	fn div(self, rhs: Self) -> Self::Output {
		if rhs.0 == 0 {
			let zero = 0;
			return Fixed128::from_parts( self.0 / zero);
		}
		let (n, d) = if rhs.0 < 0 {
			(-self.0, rhs.0.abs() as u128)
		} else {
			(self.0, rhs.0 as u128)
		};
		Fixed128::from_rational(n, d)
	}
}

impl CheckedSub for Fixed128 {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		self.0.checked_sub(rhs.0).map(Self)
	}
}

impl CheckedAdd for Fixed128 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		self.0.checked_add(rhs.0).map(Self)
	}
}

impl CheckedDiv for Fixed128 {
	fn checked_div(&self, rhs: &Self) -> Option<Self> {
		if rhs.0 == 0 {
			None
		} else {
			Some(*self / *rhs)
		}
	}
}

impl sp_std::fmt::Debug for Fixed128 {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "Fixed128({},{})", self.0 / DIV, (self.0 % DIV) / 1000)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn max() -> Fixed128 {
		Fixed128::from_parts(i128::max_value())
	}
	fn min() -> Fixed128 {
		Fixed128::from_parts(i128::min_value())
	}

	#[test]
	fn fixed128_semantics() {
		assert_eq!(Fixed128::from_rational(5, 2).0, 5 * 1_000_000_000_000_000_000 / 2);
		assert_eq!(Fixed128::from_rational(5, 2), Fixed128::from_rational(10, 4));
		assert_eq!(Fixed128::from_rational(5, 0), Fixed128::from_rational(5, 1));

		// biggest value that can be created.
		assert_ne!(max(), Fixed128::from_natural(170141183460469231731));
		assert_eq!(max(), Fixed128::from_natural(170141183460469231732));
		// smallest value that can be created
		assert_ne!(min(), Fixed128::from_natural(-170141183460469231731));
		assert_eq!(min(), Fixed128::from_natural(-170141183460469231732));
	}

	#[test]
	fn fixed_128_growth_decrease_curve() {
		let test_set = vec![0u64, 1, 10, 1000, 1_000_000_000, 1_000_000_000_000_000_000];

		// negative (1/2)
		let mut fm = Fixed128::from_rational(-1, 2);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i) as i64, i as i64 - i as i64 / 2);
		});

		// unit (1) multiplier
		fm = Fixed128::from_parts(0);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i);
		});

		// i.5 multiplier
		fm = Fixed128::from_rational(1, 2);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i * 3 / 2);
		});

		// dual multiplier
		fm = Fixed128::from_rational(1, 1);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i * 2);
		});
	}

	macro_rules! saturating_mul_acc_test {
		($num_type:tt) => {
			assert_eq!(
				Fixed128::from_rational(100, 1).saturated_multiply_accumulate(10 as $num_type),
				1010,
			);
			assert_eq!(
				Fixed128::from_rational(100, 2).saturated_multiply_accumulate(10 as $num_type),
				510,
			);
			assert_eq!(
				Fixed128::from_rational(100, 3).saturated_multiply_accumulate(0 as $num_type),
				0,
			);
			assert_eq!(
				Fixed128::from_rational(5, 1).saturated_multiply_accumulate($num_type::max_value()),
				$num_type::max_value()
			);
			assert_eq!(
				max().saturated_multiply_accumulate($num_type::max_value()),
				$num_type::max_value()
			);
		}
	}

	#[test]
	fn fixed128_multiply_accumulate_works() {
		saturating_mul_acc_test!(u64);
		saturating_mul_acc_test!(u128);
	}

	#[test]
	fn div_works() {
		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_rational(10, 1);
		assert_eq!(a / b, Fixed128::from_rational(12, 100));

		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_rational(1, 100);
		assert_eq!(a / b, Fixed128::from_rational(120, 1));

		let a = Fixed128::from_rational(12, 100);
		let b = Fixed128::from_rational(10, 1);
		assert_eq!(a / b, Fixed128::from_rational(12, 1000));

		let a = Fixed128::from_rational(12, 100);
		let b = Fixed128::from_rational(1, 100);
		assert_eq!(a / b, Fixed128::from_rational(12, 1));

		let a = Fixed128::from_rational(-12, 10);
		let b = Fixed128::from_rational(10, 1);
		assert_eq!(a / b, Fixed128::from_rational(-12, 100));

		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_rational(-10, 1);
		assert_eq!(a / b, Fixed128::from_rational(-12, 100));

		let a = Fixed128::from_rational(-12, 10);
		let b = Fixed128::from_rational(-10, 1);
		assert_eq!(a / b, Fixed128::from_rational(12, 100));
	}

	#[test]
	#[should_panic(expected = "attempt to divide by zero")]
	fn div_zero() {
		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_natural(0);
		let _ = a / b;
	}

	#[test]
	fn checked_div_zero() {
		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_natural(0);
		assert_eq!(a.checked_div(&b), None);
	}

	#[test]
	fn checked_div_non_zero() {
		let a = Fixed128::from_rational(12, 10);
		let b = Fixed128::from_rational(1, 100);
		assert_eq!(a.checked_div(&b), Some(Fixed128::from_rational(120, 1)));
	}
}
