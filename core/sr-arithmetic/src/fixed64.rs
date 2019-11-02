// Copyright 2019 Parity Technologies (UK) Ltd.
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

use rstd::{
	ops, prelude::*,
	convert::{TryFrom, TryInto},
};
use codec::{Encode, Decode};
use crate::{
	Perbill,
	traits::{
		SaturatedConversion, CheckedSub, CheckedAdd, Bounded, UniqueSaturatedInto, Saturating
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
	///
	/// This should only be used for testing.
	#[cfg(any(feature = "std", test))]
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
}

impl Saturating for Fixed64 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}
	fn saturating_mul(self, rhs: Self) -> Self {
		Self(self.0.saturating_mul(rhs.0) / DIV)
	}
	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe addition.
impl ops::Add for Fixed64 {
	type Output = Self;

	fn add(self, rhs: Self) -> Self::Output {
		Self(self.0 + rhs.0)
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe subtraction.
impl ops::Sub for Fixed64 {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		Self(self.0 - rhs.0)
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

impl rstd::fmt::Debug for Fixed64 {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		write!(f, "Fixed64({},{})", self.0 / DIV, (self.0 % DIV) / 1000)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
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
}
