// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
use num_traits::Signed;
use crate::{
	helpers_128bit::multiply_by_rational,
	Perbill,
	traits::{
		SaturatedConversion, CheckedSub, CheckedAdd, CheckedMul, CheckedDiv,
		Bounded, UniqueSaturatedInto, Saturating, FixedPointNumber
	}
};

/// An unsigned fixed point number. Can hold any value in the range [-9_223_372_036, 9_223_372_036]
/// with fixed point accuracy of one billion.
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed64(i64);

impl FixedPointNumber for Fixed64 {
	type Inner = i64;
	type PrevUnsigned = u32;
	type Unsigned = u64;
	type Perthing = Perbill;

	const DIV: i64 = 1_000_000_000;

	fn from_integer(int: Self::Inner) -> Self {
		Self(int.saturating_mul(Self::DIV))
	}

	fn from_parts(parts: Self::Inner) -> Self {
		Self(parts)
	}

	fn from_rational<N: UniqueSaturatedInto<Self::Inner>>(n: N, d: Self::Inner) -> Self {
		let n = n.unique_saturated_into();
		Self(
			(n.saturating_mul(Self::DIV) / d.max(1))
				.try_into()
				.unwrap_or_else(|_| Bounded::max_value())
		)
	}

	fn into_inner(self) -> Self::Inner {
		self.0
	}

	fn checked_mul_int<N>(&self, other: &N) -> Option<N>
	where
		N: Copy + TryFrom<Self::Inner> + TryInto<Self::Inner>,
	{
		N::try_into(*other).ok().and_then(|rhs| {
			let mut lhs = self.0;
			if lhs.is_negative() {
				lhs = lhs.saturating_mul(-1);
			}
			let mut rhs: Self::Inner = rhs.saturated_into();
			let signum = self.0.signum() * rhs.signum();
			if rhs.is_negative() {
				rhs = rhs.saturating_mul(-1);
			}

			(lhs as Self::Unsigned)
				.checked_mul(rhs as Self::Unsigned)
				.and_then(|n| n.checked_div(Self::DIV as Self::Unsigned))
				.and_then(|n| TryInto::<Self::Inner>::try_into(n).ok())
				.and_then(|n| TryInto::<N>::try_into(n * signum).ok())
		})
	}

	fn checked_div_int<N>(&self, other: &N) -> Option<N>
	where
		N: Copy + TryFrom<Self::Inner> + TryInto<Self::Inner>,
	{
		N::try_into(*other)
			.ok()
			.and_then(|n| self.0.checked_div(n))
			.and_then(|n| n.checked_div(Self::DIV))
			.and_then(|n| TryInto::<N>::try_into(n).ok())
	}

	fn saturating_mul_int<N>(&self, other: &N) -> N
	where
		N: Copy + TryFrom<Self::Inner> + TryInto<Self::Inner> + Bounded + Signed,
	{
		self.checked_mul_int(other).unwrap_or_else(|| {
			let signum = other.signum().saturated_into() * self.0.signum();
			if signum.is_negative() {
				Bounded::min_value()
			} else {
				Bounded::max_value()
			}
		})
	}

	fn saturating_abs(&self) -> Self {
		if self.0 == Self::Inner::min_value() {
			return Self::max_value();
		}

		if self.0.is_negative() {
			Self::from_parts(self.0 * -1)
		} else {
			*self
		}
	}

	fn zero() -> Self {
		Self(0)
	}

	fn is_zero(&self) -> bool {
		self.0 == 0
	}

	fn one() -> Self {
		Self(Self::DIV)
	}

	fn is_positive(&self) -> bool {
		self.0.is_positive()
	}

	fn is_negative(&self) -> bool {
		self.0.is_negative()
	}

	fn saturated_multiply_accumulate<N>(self, int: N) -> N
		where
			N: From<Self::PrevUnsigned> + TryFrom<Self::Unsigned> + UniqueSaturatedInto<Self::PrevUnsigned> +
			Bounded + Copy + Saturating +
			ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
			ops::Add<N, Output=N> + Default + core::fmt::Debug
	{
		let div = Self::DIV as Self::Unsigned;
		let positive = self.0 > 0;
		// safe to convert as absolute value.
		let parts  = self.0.checked_abs().map(|v| v as Self::Unsigned)
			.unwrap_or(Self::Inner::max_value() as Self::Unsigned + 1);

		let natural_parts = parts / div;
		let natural_parts: N = natural_parts.saturated_into();

		let fractional_parts = (parts % div) as Self::PrevUnsigned;

		let n = int.saturating_mul(natural_parts);
		let p = Self::Perthing::from_parts(fractional_parts) * int;

		// everything that needs to be either added or subtracted from the original `int`.
		let excess = n.saturating_add(p);

		if positive {
			int.saturating_add(excess)
		} else {
			int.saturating_sub(excess)
		}
	}
}

impl Saturating for Fixed64 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		self.checked_mul(&rhs).unwrap_or_else(|| {
			if (self.0.signum() * rhs.0.signum()).is_negative() {
				Bounded::min_value()
			} else {
				Bounded::max_value()
			}
		})
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}

	fn saturating_pow(self, exp: usize) -> Self {
		if exp == 0 {
			return Self::from_integer(1);
		}

		let exp = exp as u64;
		let msb_pos = 64 - exp.leading_zeros();

		let mut result = Self::from_integer(1);
		let mut pow_val = self;
		for i in 0..msb_pos {
			if ((1 << i) & exp) > 0 {
				result = result.saturating_mul(pow_val);
			}
			pow_val = pow_val.saturating_mul(pow_val);
		}
		result
	}
}

/// Use `Saturating` trait for safe addition.
impl ops::Add for Fixed64 {
	type Output = Self;

	fn add(self, rhs: Self) -> Self::Output {
		Self(self.0 + rhs.0)
	}
}

/// Use `Saturating` trait for safe subtraction.
impl ops::Sub for Fixed64 {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		Self(self.0 - rhs.0)
	}
}

/// Use `CheckedMul` trait for safe multiplication.
impl ops::Mul for Fixed64 {
	type Output = Self;

	fn mul(self, rhs: Self) -> Self::Output {
		Self(self.0 * rhs.0)
	}
}

/// Use `CheckedDiv` trait for safe division.
impl ops::Div for Fixed64 {
	type Output = Self;

	fn div(self, rhs: Self) -> Self::Output {
		if rhs.0 == 0 {
			let zero = 0;
			return Self::from_parts( self.0 / zero);
		}
		let (n, d) = if rhs.0 < 0 {
			(-self.0, rhs.0.abs())
		} else {
			(self.0, rhs.0)
		};
		Self::from_rational(n, d)
	}
}

impl CheckedSub for Fixed64 {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		self.0.checked_sub(rhs.0).map(Self)
	}
}

impl CheckedAdd for Fixed64 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		self.0.checked_add(rhs.0).map(Self)
	}
}

impl CheckedDiv for Fixed64 {
	fn checked_div(&self, rhs: &Self) -> Option<Self> {
		if rhs.0.signum() == 0 || (*self == Self::min_value() && *rhs == Self::from_integer(-1)){
			return None;
		}

		if self.0 == 0 {
			return Some(*self);
		}

		let signum = self.0.signum() / rhs.0.signum();
		let mut lhs = self.0;
		if lhs.is_negative() {
			lhs = lhs.saturating_mul(-1);
		}

		let mut rhs = rhs.0;
		if rhs.is_negative() {
			rhs = rhs.saturating_mul(-1);
		}

		multiply_by_rational(lhs as u128, <Self as FixedPointNumber>::DIV as u128, rhs as u128)
			.ok()
			.and_then(|n| TryInto::<<Self as FixedPointNumber>::Inner>::try_into(n).ok())
			.map(|n| Self(n * signum))
	}
}

impl CheckedMul for Fixed64 {
	fn checked_mul(&self, rhs: &Self) -> Option<Self> {
		let signum = self.0.signum() * rhs.0.signum();
		let mut lhs = self.0;

		if lhs.is_negative() {
			lhs = lhs.saturating_mul(-1);
		}
		let mut rhs = rhs.0;
		if rhs.is_negative() {
			rhs = rhs.saturating_mul(-1);
		}

		multiply_by_rational(lhs as u128, rhs as u128, <Self as FixedPointNumber>::DIV as u128)
			.ok()
			.and_then(|n| TryInto::<<Self as FixedPointNumber>::Inner>::try_into(n).ok())
			.map(|n| Self(n * signum))
	}
}

impl Bounded for Fixed64 {
	fn min_value() -> Self {
		Self(Bounded::min_value())
	}

	fn max_value() -> Self {
		Self(Bounded::max_value())
	}
}

impl sp_std::fmt::Debug for Fixed64 {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let integral = {
			let int = self.0 / Self::DIV;
			let signum_for_zero = if int == 0 && self.is_negative() { "-" } else { "" };
			format!("{}{}", signum_for_zero, int)
		};
		let fractional = format!("{:0>9}", (self.0 % Self::DIV).abs());
		write!(f, "Fixed64({}.{})", integral, fractional)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn max() -> Fixed64 {
		Fixed64::max_value()
	}

	fn min() -> Fixed64 {
		Fixed64::min_value()
	}

	#[test]
	fn fixed64_semantics() {
		let a = Fixed64::from_rational(5, 2);
		let b = Fixed64::from_rational(10, 4);
		assert_eq!(a.0, 5 * Fixed64::DIV / 2);
		assert_eq!(a, b);

		let a = Fixed64::from_rational(-5, 1);
		assert_eq!(a, Fixed64::from_integer(-5));

		// biggest value that can be created.
		assert_eq!(max(), Fixed64::from_parts(9_223_372_036_854_775_807));

		// the smallest value that can be created.
		assert_eq!(min(), Fixed64::from_parts(-9_223_372_036_854_775_808));
	}

	#[test]
	fn fixed64_operation() {
		let a = Fixed64::from_integer(2);
		let b = Fixed64::from_integer(1);
		assert_eq!(a.checked_add(&b), Some(Fixed64::from_integer(1 + 2)));
		assert_eq!(a.checked_sub(&b), Some(Fixed64::from_integer(2 - 1)));
		assert_eq!(a.checked_mul(&b), Some(Fixed64::from_integer(1 * 2)));
		assert_eq!(
			a.checked_div(&b),
			Some(Fixed64::from_rational(2, 1))
		);

		let a = Fixed64::from_rational(5, 2);
		let b = Fixed64::from_rational(3, 2);
		assert_eq!(
			a.checked_add(&b),
			Some(Fixed64::from_rational(8, 2))
		);
		assert_eq!(
			a.checked_sub(&b),
			Some(Fixed64::from_rational(2, 2))
		);
		assert_eq!(
			a.checked_mul(&b),
			Some(Fixed64::from_rational(15, 4))
		);
		assert_eq!(
			a.checked_div(&b),
			Some(Fixed64::from_rational(10, 6))
		);

		let a = Fixed64::from_integer(120);
		assert_eq!(a.checked_div_int(&2i32), Some(60));

		let a = Fixed64::from_rational(20, 1);
		assert_eq!(a.checked_div_int(&2i32), Some(10));

		let a = Fixed64::from_integer(120);
		assert_eq!(a.checked_mul_int(&2i32), Some(240));

		let a = Fixed64::from_rational(1, 2);
		assert_eq!(a.checked_mul_int(&20i32), Some(10));

		let a = Fixed64::from_rational(-1, 2);
		assert_eq!(a.checked_mul_int(&20i32), Some(-10));
	}

	#[test]
	fn saturating_mul_should_work() {
		let a = Fixed64::from_integer(10);
		assert_eq!(min().saturating_mul(a), min());
		assert_eq!(max().saturating_mul(a), max());

		let b = Fixed64::from_integer(-1);
		assert_eq!(Fixed64::from_integer(125).saturating_mul(b).into_inner(), -125 * Fixed64::DIV);

		let c = Fixed64::from_rational(1, 5);
		assert_eq!(Fixed64::from_integer(125).saturating_mul(c).into_inner(), 25 * Fixed64::DIV);
	}

	#[test]
	fn saturating_mul_int_works() {
		let a = Fixed64::from_rational(10, 1);
		assert_eq!(a.saturating_mul_int(&i32::max_value()), i32::max_value());

		let a = Fixed64::from_rational(-10, 1);
		assert_eq!(a.saturating_mul_int(&i32::max_value()), i32::min_value());

		let a = Fixed64::from_rational(3, 1);
		assert_eq!(a.saturating_mul_int(&100i8), i8::max_value());

		let a = Fixed64::from_rational(10, 1);
		assert_eq!(a.saturating_mul_int(&123i128), 1230);

		let a = Fixed64::from_rational(-10, 1);
		assert_eq!(a.saturating_mul_int(&123i128), -1230);

		assert_eq!(max().saturating_mul_int(&2i128), 18_446_744_073);
		assert_eq!(min().saturating_mul_int(&2i128), -18_446_744_073);

		assert_eq!(max().saturating_mul_int(&i64::min_value()), i64::min_value());
		assert_eq!(min().saturating_mul_int(&i64::max_value()), i64::min_value());
		assert_eq!(min().saturating_mul_int(&i64::min_value()), i64::max_value());

		assert_eq!(max().saturating_mul_int(&i128::min_value()), i128::min_value());
		assert_eq!(min().saturating_mul_int(&i128::max_value()), i128::min_value());
		assert_eq!(min().saturating_mul_int(&i128::min_value()), i128::max_value());
	}

	#[test]
	fn zero_works() {
		assert_eq!(Fixed64::zero(), Fixed64::from_integer(0));
	}

	#[test]
	fn is_zero_works() {
		assert!(Fixed64::zero().is_zero());
		assert!(!Fixed64::from_integer(1).is_zero());
	}

	#[test]
	fn checked_div_with_zero_should_be_none() {
		let a = Fixed64::from_integer(1);
		let b = Fixed64::from_integer(0);

		assert_eq!(a.checked_div(&b), None);
		assert_eq!(b.checked_div(&a), Some(b));

		let c = Fixed64::from_integer(-1);

		assert_eq!((Fixed64::min_value() + Fixed64::from_rational(1, Fixed64::accuracy())).checked_div(&c), Some(Fixed64::max_value()));
		assert_eq!(Fixed64::min_value().checked_div(&c), None);
		assert_eq!((Fixed64::one()).checked_div(&Fixed64::zero()), None);
	}

	#[test]
	fn checked_div_int_with_zero_should_be_none() {
		let a = Fixed64::from_integer(1);
		assert_eq!(a.checked_div_int(&0i32), None);
		let a = Fixed64::from_integer(0);
		assert_eq!(a.checked_div_int(&1i32), Some(0));
	}

	#[test]
	fn fixed_64_growth_decrease_curve() {
		let test_set = vec![0u32, 1, 10, 1000, 1_000_000_000];

		// negative (1/2)
		let mut fm = Fixed64::from_rational(-1, 2);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i) as i32, i as i32 - i as i32 / 2);
		});

		// unit (1) multiplier
		fm = Fixed64::from_parts(0);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i);
		});

		// i.5 multiplier
		fm = Fixed64::from_rational(1, 2);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i * 3 / 2);
		});

		// dual multiplier
		fm = Fixed64::from_rational(1, 1);
		test_set.clone().into_iter().for_each(|i| {
			assert_eq!(fm.saturated_multiply_accumulate(i), i * 2);
		});
	}

	macro_rules! saturating_mul_acc_test {
		($num_type:tt) => {
			assert_eq!(
				Fixed64::from_rational(100, 1).saturated_multiply_accumulate(10 as $num_type),
				1010,
			);
			assert_eq!(
				Fixed64::from_rational(100, 2).saturated_multiply_accumulate(10 as $num_type),
				510,
			);
			assert_eq!(
				Fixed64::from_rational(100, 3).saturated_multiply_accumulate(0 as $num_type),
				0,
			);
			assert_eq!(
				Fixed64::from_rational(5, 1).saturated_multiply_accumulate($num_type::max_value()),
				$num_type::max_value()
			);
			assert_eq!(
				max().saturated_multiply_accumulate($num_type::max_value()),
				$num_type::max_value()
			);
		}
	}

	#[test]
	fn fixed64_multiply_accumulate_works() {
		saturating_mul_acc_test!(u32);
		saturating_mul_acc_test!(u64);
		saturating_mul_acc_test!(u128);
	}

	#[test]
	fn div_works() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_rational(10, 1);
		assert_eq!(a / b, Fixed64::from_rational(12, 100));

		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_rational(1, 100);
		assert_eq!(a / b, Fixed64::from_rational(120, 1));

		let a = Fixed64::from_rational(12, 100);
		let b = Fixed64::from_rational(10, 1);
		assert_eq!(a / b, Fixed64::from_rational(12, 1000));

		let a = Fixed64::from_rational(12, 100);
		let b = Fixed64::from_rational(1, 100);
		assert_eq!(a / b, Fixed64::from_rational(12, 1));

		let a = Fixed64::from_rational(-12, 10);
		let b = Fixed64::from_rational(10, 1);
		assert_eq!(a / b, Fixed64::from_rational(-12, 100));

		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_rational(-10, 1);
		assert_eq!(a / b, Fixed64::from_rational(-12, 100));

		let a = Fixed64::from_rational(-12, 10);
		let b = Fixed64::from_rational(-10, 1);
		assert_eq!(a / b, Fixed64::from_rational(12, 100));
	}

	#[test]
	#[should_panic(expected = "attempt to divide by zero")]
	fn div_zero() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_integer(0);
		let _ = a / b;
	}

	#[test]
	fn checked_div_zero() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_integer(0);
		assert_eq!(a.checked_div(&b), None);
	}

	#[test]
	fn checked_div_non_zero() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_rational(1, 100);
		assert_eq!(a.checked_div(&b), Some(Fixed64::from_rational(120, 1)));
	}

	#[test]
	fn saturating_pow_should_work() {
		assert_eq!(Fixed64::from_integer(2).saturating_pow(0), Fixed64::from_integer(1));
		assert_eq!(Fixed64::from_integer(2).saturating_pow(1), Fixed64::from_integer(2));
		assert_eq!(Fixed64::from_integer(2).saturating_pow(2), Fixed64::from_integer(4));
		assert_eq!(Fixed64::from_integer(2).saturating_pow(3), Fixed64::from_integer(8));
		assert_eq!(Fixed64::from_integer(2).saturating_pow(33), Fixed64::from_integer(8589934592));

		// Saturating.
		assert_eq!(Fixed64::from_integer(2).saturating_pow(49), Fixed64::from_integer(562949953421312));

		assert_eq!(Fixed64::from_integer(1).saturating_pow(1000), Fixed64::from_integer(1));
		assert_eq!(Fixed64::from_integer(-1).saturating_pow(1000), Fixed64::from_integer(1));
		assert_eq!(Fixed64::from_integer(-1).saturating_pow(1001), Fixed64::from_integer(-1));
		assert_eq!(Fixed64::from_integer(1).saturating_pow(usize::max_value()), Fixed64::from_integer(1));
		assert_eq!(Fixed64::from_integer(-1).saturating_pow(usize::max_value()), Fixed64::from_integer(-1));
		assert_eq!(Fixed64::from_integer(-1).saturating_pow(usize::max_value() - 1), Fixed64::from_integer(1));

		assert_eq!(Fixed64::from_integer(114209).saturating_pow(3), Fixed64::from_integer(1489707440031329));
		assert_eq!(Fixed64::from_integer(114209).saturating_pow(4), Fixed64::max_value());

		assert_eq!(Fixed64::from_integer(1).saturating_pow(usize::max_value()), Fixed64::from_integer(1));
		assert_eq!(Fixed64::from_integer(0).saturating_pow(usize::max_value()), Fixed64::from_integer(0));
		assert_eq!(Fixed64::from_integer(2).saturating_pow(usize::max_value()), Fixed64::max_value());
	}
}
