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
use crate::{
	Perbill,
	traits::{
		SaturatedConversion, CheckedSub, CheckedAdd, CheckedDiv, Bounded, UniqueSaturatedInto, Saturating
	}
};

/// An unsigned fixed point number. Can hold any value in the range [-9_223_372_036, 9_223_372_036]
/// with fixed point accuracy of one billion.
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed64(i64);

/// The accuracy of the `Fixed64` type.
const DIV: i64 = 1_000_000_000;

impl Fixed64 {
	/// creates self from a natural number.
	///
	/// Note that this might be lossy.
	pub fn from_natural(int: i64) -> Self {
		Self(int.saturating_mul(DIV))
	}

	/// Return the accuracy of the type. Given that this function returns the value `X`, it means
	/// that an instance composed of `X` parts (`Fixed64::from_parts(X)`) is equal to `1`.
	pub fn accuracy() -> i64 {
		DIV
	}

	/// Consume self and return the inner value.
	pub fn into_inner(self) -> i64 { self.0 }

	/// Raw constructor. Equal to `parts / 1_000_000_000`.
	pub fn from_parts(parts: i64) -> Self {
		Self(parts)
	}

	/// creates self from a rational number. Equal to `n/d`.
	///
	/// Note that this might be lossy.
	pub fn from_rational(n: i64, d: u64) -> Self {
		Self(
			(i128::from(n).saturating_mul(i128::from(DIV)) / i128::from(d).max(1))
				.try_into()
				.unwrap_or_else(|_| Bounded::max_value())
		)
	}

	/// Performs a saturated multiply and accumulate by unsigned number.
	///
	/// Returns a saturated `int + (self * int)`.
	pub fn saturated_multiply_accumulate<N>(self, int: N) -> N
		where
			N: TryFrom<u64> + From<u32> + UniqueSaturatedInto<u32> + Bounded + Clone + Saturating +
			ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
			ops::Add<N, Output=N>,
	{
		let div = DIV as u64;
		let positive = self.0 > 0;
		// safe to convert as absolute value.
		let parts = self.0.checked_abs().map(|v| v as u64).unwrap_or(i64::max_value() as u64 + 1);


		// will always fit.
		let natural_parts = parts / div;
		// might saturate.
		let natural_parts: N = natural_parts.saturated_into();
		// fractional parts can always fit into u32.
		let perbill_parts = (parts % div) as u32;

		let n = int.clone().saturating_mul(natural_parts);
		let p = Perbill::from_parts(perbill_parts) * int.clone();

		// everything that needs to be either added or subtracted from the original weight.
		let excess = n.saturating_add(p);

		if positive {
			int.saturating_add(excess)
		} else {
			int.saturating_sub(excess)
		}
	}

	pub fn is_negative(&self) -> bool {
		self.0.is_negative()
	}
}

impl Saturating for Fixed64 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		let a = self.0 as i128;
		let b = rhs.0 as i128;
		let res = a * b / DIV as i128;
		Self(res.saturated_into())
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}

	fn saturating_pow(self, exp: usize) -> Self {
		if exp == 0 {
			return Self::from_natural(1);
		}

		let exp = exp as u64;
		let msb_pos = 64 - exp.leading_zeros();

		let mut result = Self::from_natural(1);
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

/// Use `CheckedDiv` trait for safe division.
impl ops::Div for Fixed64 {
	type Output = Self;

	fn div(self, rhs: Self) -> Self::Output {
		if rhs.0 == 0 {
			panic!("attempt to divide by zero");
		}
		let (n, d) = if rhs.0 < 0 {
			(-self.0, rhs.0.abs() as u64)
		} else {
			(self.0, rhs.0 as u64)
		};
		Fixed64::from_rational(n, d)
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
		if rhs.0 == 0 {
			None
		} else {
			Some(*self / *rhs)
		}
	}
}

impl sp_std::fmt::Debug for Fixed64 {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let integral = {
			let int = self.0 / DIV;
			let signum_for_zero = if int == 0 && self.is_negative() { "-" } else { "" };
			format!("{}{}", signum_for_zero, int)
		};
		let fractional = format!("{:0>9}", (self.0 % DIV).abs());
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
		Fixed64::from_parts(i64::max_value())
	}

	#[test]
	fn fixed64_semantics() {
		assert_eq!(Fixed64::from_rational(5, 2).0, 5 * 1_000_000_000 / 2);
		assert_eq!(Fixed64::from_rational(5, 2), Fixed64::from_rational(10, 4));
		assert_eq!(Fixed64::from_rational(5, 0), Fixed64::from_rational(5, 1));

		// biggest value that can be created.
		assert_ne!(max(), Fixed64::from_natural(9_223_372_036));
		assert_eq!(max(), Fixed64::from_natural(9_223_372_037));
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
		let b = Fixed64::from_natural(0);
		let _ = a / b;
	}

	#[test]
	fn checked_div_zero() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_natural(0);
		assert_eq!(a.checked_div(&b), None);
	}

	#[test]
	fn checked_div_non_zero() {
		let a = Fixed64::from_rational(12, 10);
		let b = Fixed64::from_rational(1, 100);
		assert_eq!(a.checked_div(&b), Some(Fixed64::from_rational(120, 1)));
	}

	#[test]
	fn saturating_mul_should_work() {
		assert_eq!(Fixed64::from_natural(100).saturating_mul(Fixed64::from_natural(100)), Fixed64::from_natural(10000));
	}

	#[test]
	fn saturating_pow_should_work() {
		assert_eq!(Fixed64::from_natural(2).saturating_pow(0), Fixed64::from_natural(1));
		assert_eq!(Fixed64::from_natural(2).saturating_pow(1), Fixed64::from_natural(2));
		assert_eq!(Fixed64::from_natural(2).saturating_pow(2), Fixed64::from_natural(4));
		assert_eq!(Fixed64::from_natural(2).saturating_pow(3), Fixed64::from_natural(8));
		assert_eq!(Fixed64::from_natural(2).saturating_pow(20), Fixed64::from_natural(1048576));

		assert_eq!(Fixed64::from_natural(1).saturating_pow(1000), Fixed64::from_natural(1));
		assert_eq!(Fixed64::from_natural(-1).saturating_pow(1000), Fixed64::from_natural(1));
		assert_eq!(Fixed64::from_natural(-1).saturating_pow(1001), Fixed64::from_natural(-1));
		assert_eq!(Fixed64::from_natural(1).saturating_pow(usize::max_value()), Fixed64::from_natural(1));
		assert_eq!(Fixed64::from_natural(-1).saturating_pow(usize::max_value()), Fixed64::from_natural(-1));
		assert_eq!(Fixed64::from_natural(-1).saturating_pow(usize::max_value() - 1), Fixed64::from_natural(1));

		assert_eq!(Fixed64::from_natural(309).saturating_pow(4), Fixed64::from_natural(9_116_621_361));
		assert_eq!(Fixed64::from_natural(309).saturating_pow(5), Fixed64::from_parts(i64::max_value()));

		assert_eq!(Fixed64::from_natural(1).saturating_pow(usize::max_value()), Fixed64::from_natural(1));
		assert_eq!(Fixed64::from_natural(0).saturating_pow(usize::max_value()), Fixed64::from_natural(0));
		assert_eq!(Fixed64::from_natural(2).saturating_pow(usize::max_value()), Fixed64::from_parts(i64::max_value()));
	}
}
