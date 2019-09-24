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

//! Minimal fixed point arithmetic primitives and types for runtime.

#[cfg(feature = "std")]
use crate::serde::{Serialize, Deserialize};

use rstd::{
	ops, prelude::*,
	convert::{TryInto, TryFrom},
	cmp::Ordering,
};
use codec::{Encode, Decode};
use crate::traits::{
	SaturatedConversion, CheckedSub, CheckedAdd, Bounded, UniqueSaturatedInto, Saturating, Zero,
};

macro_rules! implement_per_thing {
	($name:ident, $test_mod:ident, [$($test_units:tt),+], $max:tt, $type:ty, $upper_type:ty, $title:expr $(,)?) => {
		/// A fixed point representation of a number between in the range [0, 1].
		///
		#[doc = $title]
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Ord, PartialOrd))]
		#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
		pub struct $name($type);

		impl $name {
			/// Nothing.
			pub fn zero() -> Self { Self(0) }

			/// `true` if this is nothing.
			pub fn is_zero(&self) -> bool { self.0 == 0 }

			/// Everything.
			pub fn one() -> Self { Self($max) }

			/// Consume self and deconstruct into a raw numeric type.
			pub fn deconstruct(self) -> $type { self.0 }

			/// Return the scale at which this per-thing is working.
			pub const fn accuracy() -> $type { $max }

			/// From an explicitly defined number of parts per maximum of the type.
			///
			/// This can be called at compile time.
			pub const fn from_parts(parts: $type) -> Self {
				Self([parts, $max][(parts > $max) as usize])
			}

			/// Converts from a percent. Equal to `x / 100`.
			///
			/// This can be created at compile time.
			pub const fn from_percent(x: $type) -> Self {
				Self([x, 100][(x > 100) as usize] * ($max / 100))
			}

			/// Return the product of multiplication of this value by itself.
			pub fn square(self) -> Self {
				// both can be safely casted and multiplied.
				let p: $upper_type = self.0 as $upper_type * self.0 as $upper_type;
				let q: $upper_type = $max as $upper_type * $max as $upper_type;
				Self::from_rational_approximation(p, q)
			}

			/// Converts a fraction into `Permill`.
			#[cfg(feature = "std")]
			pub fn from_fraction(x: f64) -> Self { Self((x * ($max as f64)) as $type) }

			/// Approximate the fraction `p/q` into a per-thing fraction. This will never overflow.
			///
			/// The computation of this approximation is performed in the generic type `N`. Given
			/// `M` as the data type that can hold the maximum value of this per-thing (e.g. u32 for
			/// perbill), this can only work if `N == M` or `N: From<M> + TryInto<M>`.
			pub fn from_rational_approximation<N>(p: N, q: N) -> Self
				where N: Clone + Ord + From<$type> + TryInto<$type> + ops::Div<N, Output=N>
			{
				// q cannot be zero.
				let q = q.max((1 as $type).into());
				// p should not be bigger than q.
				let p = p.min(q.clone());

				let factor = (q.clone() / $max.into()).max((1 as $type).into());

				// q cannot overflow: (q / (q/$max)) < 2 * $max. p < q hence p also cannot overflow.
				// this implies that $type must be able to fit 2 * $max.
				let q_reduce: $type = (q / factor.clone())
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"q / (q/$max) < (2 * $max). Macro prevents any type being created that \
						does not satisfy this; qed"
					);
				let p_reduce: $type = (p / factor.clone())
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"q / (q/$max) < (2 * $max). Macro prevents any type being created that \
						does not satisfy this; qed"
					);

				// `p_reduced` and `q_reduced` are withing $type. Mul by another $max will always
				// fit in $upper_type. This is guaranteed by the macro tests.
				let part =
					p_reduce as $upper_type
					* ($max as $upper_type)
					/ q_reduce as $upper_type;

				$name(part as $type)
			}
		}

		impl Saturating for $name {
			fn saturating_add(self, rhs: Self) -> Self {
				// defensive-only: since `$max * 2 < $type::max_value()`, this can never overflow.
				Self::from_parts(self.0.saturating_add(rhs.0))
			}
			fn saturating_sub(self, rhs: Self) -> Self {
				Self::from_parts(self.0.saturating_sub(rhs.0))
			}
			fn saturating_mul(self, rhs: Self) -> Self {
				let a = self.0 as $upper_type;
				let b = rhs.0 as $upper_type;
				let m = $max as $upper_type;
				let parts = a * b / m;
				// This will always fit into $type.
				Self::from_parts(parts as $type)
			}
		}

		impl ops::Div for $name {
			type Output = Self;

			fn div(self, rhs: Self) -> Self::Output {
				let p = self.0;
				let q = rhs.0;
				Self::from_rational_approximation(p, q)
			}
		}

		/// Overflow-prune multiplication.
		///
		/// tailored to be used with a balance type.
		impl<N> ops::Mul<N> for $name
		where
			N: Clone + From<$type> + UniqueSaturatedInto<$type> + ops::Rem<N, Output=N>
				+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
		{
			type Output = N;
			fn mul(self, b: N) -> Self::Output {
				let maximum: N = $max.into();
				let upper_max: $upper_type = $max.into();
				let part: N = self.0.into();

				let rem_multiplied_divided = {
					let rem = b.clone().rem(maximum.clone());

					// `rem_sized` is inferior to $max, thus it fits into $type. This is assured by
					// a test.
					let rem_sized = rem.saturated_into::<$type>();

					// `self` and `rem_sized` are inferior to $max, thus the product is less than
					// $max^2 and fits into $upper_type. This is assured by a test.
					let rem_multiplied_upper = rem_sized as $upper_type * self.0 as $upper_type;

					// `rem_multiplied_upper` is less than $max^2 therefore divided by $max it fits
					// in $type. remember that $type always fits $max.
					let mut rem_multiplied_divided_sized =
						(rem_multiplied_upper / upper_max) as $type;
					// fix a tiny rounding error
					if rem_multiplied_upper % upper_max > upper_max / 2 {
						rem_multiplied_divided_sized += 1;
					}

					// `rem_multiplied_divided_sized` is inferior to b, thus it can be converted
					// back to N type
					rem_multiplied_divided_sized.into()
				};

				(b / maximum) * part + rem_multiplied_divided
			}
		}

		impl codec::CompactAs for $name {
			type As = $type;
			fn encode_as(&self) -> &$type {
				&self.0
			}
			fn decode_from(x: $type) -> Self {
				Self(x)
			}
		}

		impl From<codec::Compact<$name>> for $name {
			fn from(x: codec::Compact<$name>) -> Self {
				x.0
			}
		}

		#[cfg(test)]
		mod $test_mod {
			use codec::{Encode, Decode};
			use super::{$name, Saturating};
			use crate::{assert_eq_error_rate, traits::Zero};


			#[test]
			fn macro_expanded_correctly() {
				// needed for the `from_percent` to work.
				assert!($max >= 100);
				assert!($max % 100 == 0);

				// needed for `from_rational_approximation`
				assert!(2 * $max < <$type>::max_value());
				assert!(($max as $upper_type) < <$upper_type>::max_value());

				// for something like percent they can be the same.
				assert!((<$type>::max_value() as $upper_type) <= <$upper_type>::max_value());
				assert!(($max as $upper_type).checked_mul($max.into()).is_some());
			}

			#[derive(Encode, Decode, PartialEq, Eq, Debug)]
			struct WithCompact<T: crate::codec::HasCompact> {
				data: T,
			}

			#[test]
			fn has_compact() {
				let data = WithCompact { data: $name(1) };
				let encoded = data.encode();
				assert_eq!(data, WithCompact::<$name>::decode(&mut &encoded[..]).unwrap());
			}

			#[test]
			fn compact_encoding() {
				let tests = [
					// assume all per_things have the size u8 at least.
					(0 as $type, 1usize),
					(1 as $type, 1usize),
					(63, 1),
					(64, 2),
					(65, 2),
					(<$type>::max_value(), <$type>::max_value().encode().len() + 1)
				];
				for &(n, l) in &tests {
					let compact: crate::codec::Compact<$name> = $name(n).into();
					let encoded = compact.encode();
					assert_eq!(encoded.len(), l);
					let decoded = <crate::codec::Compact<$name>>::decode(&mut & encoded[..])
						.unwrap();
					let per_thingy: $name = decoded.into();
					assert_eq!(per_thingy, $name(n));
				}
			}

			#[test]
			fn per_thing_api_works() {
				// some really basic stuff
				assert_eq!($name::zero(), $name::from_parts(Zero::zero()));
				assert_eq!($name::one(), $name::from_parts($max));
				assert_eq!($name::accuracy(), $max);
				assert_eq!($name::from_percent(0), $name::from_parts(Zero::zero()));
				assert_eq!($name::from_percent(10), $name::from_parts($max / 10));
				assert_eq!($name::from_percent(100), $name::from_parts($max));
			}

			macro_rules! per_thing_mul_test {
				($num_type:tt) => {
					// multiplication from all sort of from_percent
					assert_eq!(
						$name::from_percent(100) * $num_type::max_value(),
						$num_type::max_value()
					);
					assert_eq_error_rate!(
						$name::from_percent(99) * $num_type::max_value(),
						((Into::<U256>::into($num_type::max_value()) * 99u32) / 100u32).as_u128() as $num_type,
						1,
					);
					assert_eq!(
						$name::from_percent(50) * $num_type::max_value(),
						$num_type::max_value() / 2,
					);
					assert_eq_error_rate!(
						$name::from_percent(1) * $num_type::max_value(),
						$num_type::max_value() / 100,
						1,
					);
					assert_eq!($name::from_percent(0) * $num_type::max_value(), 0);

					// // multiplication with bounds
					assert_eq!($name::one() * $num_type::max_value(), $num_type::max_value());
					assert_eq!($name::zero() * $num_type::max_value(), 0);
				}
			}

			#[test]
			fn per_thing_mul_works() {
				use primitive_types::U256;

				// accuracy test
				assert_eq!($name::from_rational_approximation(1 as $type, 3) * 30 as $type, 10);

				$(per_thing_mul_test!($test_units);)*
			}

			#[test]
			fn per_thing_mul_rounds_to_nearest_number() {
				assert_eq!($name::from_percent(33) * 10u64, 3);
				assert_eq!($name::from_percent(34) * 10u64, 3);
				assert_eq!($name::from_percent(35) * 10u64, 3);
				assert_eq!($name::from_percent(36) * 10u64, 4);
				assert_eq!($name::from_percent(36) * 10u64, 4);
			}

			#[test]
			fn per_thing_multiplication_with_large_number() {
				use primitive_types::U256;
				let max_minus_one = $max - 1;
				assert_eq_error_rate!(
					$name::from_parts(max_minus_one) * std::u128::MAX,
					((Into::<U256>::into(std::u128::MAX) * max_minus_one) / $max).as_u128(),
					1,
				);
			}

			macro_rules! per_thing_from_rationale_approx_test {
				($num_type:tt) => {
					// within accuracy boundary
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 0),
						$name::one(),
					);
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 1),
						$name::one(),
					);
					assert_eq_error_rate!(
						$name::from_rational_approximation(1 as $num_type, 3).0,
						$name::from_parts($max / 3).0,
						2
					);
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 10),
						$name::from_percent(10),
					);
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 4),
						$name::from_percent(25),
					);
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 4),
						$name::from_rational_approximation(2 as $num_type, 8),
					);
					// no accurate anymore but won't overflow.
					assert_eq!(
						$name::from_rational_approximation(
							$num_type::max_value() - 1,
							$num_type::max_value()
						),
						$name::one(),
					);
					assert_eq_error_rate!(
						$name::from_rational_approximation(
							$num_type::max_value() / 3,
							$num_type::max_value()
						).0,
						$name::from_parts($max / 3).0,
						2
					);
					assert_eq!(
						$name::from_rational_approximation(1, $num_type::max_value()),
						$name::zero(),
					);
				};
			}

			#[test]
			fn per_thing_from_rationale_approx_works() {
				// This is just to make sure something like Percent which _might_ get built from a
				// u8 does not overflow in the context of this test.
				let max_value = $max as $upper_type;
				// almost at the edge
				assert_eq!(
					$name::from_rational_approximation($max - 1, $max + 1),
					$name::from_parts($max - 2),
				);
				assert_eq!(
					$name::from_rational_approximation(1, $max-1),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational_approximation(1, $max),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational_approximation(2, 2 * $max - 1),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational_approximation(1, $max+1),
					$name::zero(),
				);
				assert_eq!(
					$name::from_rational_approximation(3 * max_value / 2, 3 * max_value),
					$name::from_percent(50),
				);
				$(per_thing_from_rationale_approx_test!($test_units);)*
			}

			#[test]
			fn per_things_mul_operates_in_output_type() {
				// assert_eq!($name::from_percent(50) * 100u32, 50u32);
				assert_eq!($name::from_percent(50) * 100u64, 50u64);
				assert_eq!($name::from_percent(50) * 100u128, 50u128);
			}

			#[test]
			fn per_thing_saturating_op_works() {
				assert_eq!(
					$name::from_percent(50).saturating_add($name::from_percent(40)),
					$name::from_percent(90)
				);
				assert_eq!(
					$name::from_percent(50).saturating_add($name::from_percent(50)),
					$name::from_percent(100)
				);
				assert_eq!(
					$name::from_percent(60).saturating_add($name::from_percent(50)),
					$name::from_percent(100)
				);

				assert_eq!(
					$name::from_percent(60).saturating_sub($name::from_percent(50)),
					$name::from_percent(10)
				);
				assert_eq!(
					$name::from_percent(60).saturating_sub($name::from_percent(60)),
					$name::from_percent(0)
				);
				assert_eq!(
					$name::from_percent(60).saturating_sub($name::from_percent(70)),
					$name::from_percent(0)
				);

				assert_eq!(
					$name::from_percent(50).saturating_mul($name::from_percent(50)),
					$name::from_percent(25)
				);
				assert_eq!(
					$name::from_percent(20).saturating_mul($name::from_percent(20)),
					$name::from_percent(4)
				);
				assert_eq!(
					$name::from_percent(10).saturating_mul($name::from_percent(10)),
					$name::from_percent(1)
				);
			}

			#[test]
			fn per_thing_square_works() {
				assert_eq!($name::from_percent(100).square(), $name::from_percent(100));
				assert_eq!($name::from_percent(50).square(), $name::from_percent(25));
				assert_eq!($name::from_percent(10).square(), $name::from_percent(1));
				assert_eq!(
					$name::from_percent(2).square(),
					$name::from_parts((4 * ($max as $upper_type) / 100 / 100) as $type)
				);
			}

			#[test]
			fn per_things_div_works() {
				// normal
				assert_eq!($name::from_percent(10) / $name::from_percent(20),
					$name::from_percent(50)
				);
				assert_eq!($name::from_percent(10) / $name::from_percent(10),
					$name::from_percent(100)
				);
				assert_eq!($name::from_percent(10) / $name::from_percent(0),
					$name::from_percent(100)
				);

				// will not overflow
				assert_eq!($name::from_percent(10) / $name::from_percent(5),
					$name::from_percent(100)
				);
				assert_eq!($name::from_percent(100) / $name::from_percent(50),
					$name::from_percent(100)
				);
			}
		}
	};
}

implement_per_thing!(
	Percent,
	test_per_cent,
	[u32, u64, u128],
	100u8,
	u8,
	u16,
	"_Percent_",
);
implement_per_thing!(
	Permill,
	test_permill,
	[u32, u64, u128],
	1_000_000u32,
	u32,
	u64,
	"_Parts per Million_",
);
implement_per_thing!(
	Perbill,
	test_perbill,
	[u32, u64, u128],
	1_000_000_000u32,
	u32,
	u64,
	"_Parts per Billion_",
);
implement_per_thing!(
	Perquintill,
	test_perquintill,
	[u64, u128],
	1_000_000_000_000_000_000u64,
	u64,
	u128,
	"_Parts per Quintillion_",
);

/// An unsigned fixed point number. Can hold any value in the range [-9_223_372_036, 9_223_372_036]
/// with fixed point accuracy of one billion.
#[cfg_attr(feature = "std", derive(Debug))]
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

	/// Raw constructor. Equal to `parts / 1_000_000_000`.
	pub fn from_parts(parts: i64) -> Self {
		Self(parts)
	}

	/// creates self from a rational number. Equal to `n/d`.
	///
	/// Note that this might be lossy.
	pub fn from_rational(n: i64, d: u64) -> Self {
		Self(
			((n as i128).saturating_mul(DIV as i128) / (d as i128).max(1))
			.try_into()
			.unwrap_or(Bounded::max_value())
		)
	}

	/// Performs a saturated multiply and accumulate by unsigned number.
	///
	/// Returns a saturated `int + (self * int)`.
	pub fn saturated_multiply_accumulate<N>(&self, int: N) -> N
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
		if let Some(v) = self.0.checked_sub(rhs.0) {
			Some(Self(v))
		} else {
			None
		}
	}
}

impl CheckedAdd for Fixed64 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		if let Some(v) = self.0.checked_add(rhs.0) {
			Some(Self(v))
		} else {
			None
		}
	}
}

/// Some helper functions to work with 128bit numbers. Note that the functionality provided here is
/// only sensible to use with 128bit numbers because for smaller sizes, you can always rely on
/// assumptions of a bigger type (u128) being available, or simply create a per-thing and use the
/// multiplication implementation provided there.
pub mod helpers_128bit {
	use super::Perquintill;
	use crate::traits::Zero;
	use rstd::cmp::{min, max};

	const ERROR: &'static str = "can not accurately multiply by rational in this type";

	/// Helper gcd function used in Rational128 implementation.
	pub fn gcd(a: u128, b: u128) -> u128 {
		match ((a, b), (a & 1, b & 1)) {
			((x, y), _) if x == y => y,
			((0, x), _) | ((x, 0), _) => x,
			((x, y), (0, 1)) | ((y, x), (1, 0)) => gcd(x >> 1, y),
			((x, y), (0, 0)) => gcd(x >> 1, y >> 1) << 1,
			((x, y), (1, 1)) => {
				let (x, y) = (min(x, y), max(x, y));
				gcd((y - x) >> 1, x)
			},
			_ => unreachable!(),
		}
	}

	/// Safely and accurately compute `a * b / c`. The approach is:
	///   - Simply try `a * b / c`.
	///   - Else, swap the operations (divide first) if `a > c` (division is possible) and `b <= c`
	///     (overflow cannot happen)
	///   - At any point, given an overflow or accuracy loss, return an Error.
	///
	/// Invariant: c must be greater than or equal to 1.
	/// This might not return Ok even if `b < c`.
	pub fn multiply_by_rational(a: u128, b: u128, c: u128) -> Result<u128, &'static str> {
		if a.is_zero() || b.is_zero() { return Ok(Zero::zero()); }

		// invariant: C cannot be zero.
		let c = c.max(1);

		// a and b are interchangeable by definition in this function. It always helps to assume the
		// bigger of which is being multiplied by a `0 < b/c < 1`. Hence, a should be the bigger and
		// b the smaller one.
		let t = a;
		let a = a.max(b);
		let b = t.min(b);

		if let Some(x) = a.checked_mul(b) {
			// This is the safest way to go. Try it.
			Ok(x / c)
		} else if a > c {
			// if it can be safely swapped and it is a fraction, then swap.
			let q = a / c;
			let r = a % c;
			let r_additional = multiply_by_rational(r, b, c)?;

			let q_part = q.checked_mul(b)
				.ok_or(ERROR)?;
			let result = q_part.checked_add(r_additional)
				.ok_or(ERROR)?;
			Ok(result)
		} else {
			Err(ERROR)
		}
	}

	/// Performs [`multiply_by_rational`]. In case of failure, if `b < c` it tries to approximate
	/// the ratio into a perquintillion and return a lossy result. Otherwise, a best effort approach
	/// of shifting both b and c is performed until multiply_by_rational can work.
	///
	/// This function can very well be lossy and as the name suggests, perform a best effort in the
	/// scope of u128 numbers. In case `b > c` and overflow happens, `a` is returned.
	///
	/// c must be greater than or equal to 1.
	pub fn multiply_by_rational_best_effort(a: u128, b: u128, c: u128) -> u128 {
		if a.is_zero() || b.is_zero() { return Zero::zero(); }
		let c = c.max(1);

		// unwrap the loop once. This favours performance over readability.
		multiply_by_rational(a, b, c).unwrap_or_else(|_| {
			if b <= c {
				let per_thing = Perquintill::from_rational_approximation(b, c);
				per_thing * a
			} else {
				let mut shift = 1;
				let mut shifted_b = b.checked_shr(shift).unwrap_or(0);
				let mut shifted_c = c.checked_shr(shift).unwrap_or(0);

				loop {
					if shifted_b.is_zero() || shifted_c.is_zero() {
						break a
					}
					match multiply_by_rational(a, shifted_b, shifted_c) {
						Ok(r) => break r,
						Err(_) => {
							shift = shift + 1;
							// by the time we reach here, b >= 1 && c >= 1. Before panic, they have
							// to be zero which is prevented to happen by the break.
							shifted_b = b.checked_shr(shift)
								.expect(
									"b >= 1 && c >= 1; break prevents them from ever being zero; \
									panic can only happen after either is zero; qed"
								);
							shifted_c = c.checked_shr(shift)
								.expect(
									"b >= 1 && c >= 1; break prevents them from ever being zero; \
									panic can only happen after either is zero; qed"
								);
						}
					}
				}
			}
		})
	}
}

/// A wrapper for any rational number with a 128 bit numerator and denominator.
#[derive(Clone, Copy, Default, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Rational128(u128, u128);

impl Rational128 {
	/// Nothing.
	pub fn zero() -> Self {
		Self(0, 1)
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
			if den > self.1 {
				let n = helpers_128bit::multiply_by_rational(self.0, den, self.1)?;
				Ok(Self(n, den))
			} else {
				let div = self.1 / den;
				Ok(Self(self.0 / div.max(1), den))
			}
		}
	}

	/// Get the least common divisor of `self` and `other`.
	///
	/// This only returns if the result is accurate. `Err` is returned if the result cannot be
	/// accurately calculated.
	pub fn lcm(&self, other: &Self) -> Result<u128, &'static str> {
		// this should be tested better: two large numbers that are almost the same.
		if self.1 == other.1 { return Ok(self.1) }
		let g = helpers_128bit::gcd(self.1, other.1);
		helpers_128bit::multiply_by_rational(self.1 , other.1, g)
	}

	/// A saturating add that assumes `self` and `other` have the same denominator.
	pub fn lazy_saturating_add(self, other: Self) -> Self {
		if other.is_zero() {
			self
		} else {
			Self(self.0.saturating_add(other.0) ,self.1)
		}
	}

	/// A saturating subtraction that assumes `self` and `other` have the same denominator.
	pub fn lazy_saturating_sub(self, other: Self) -> Self {
		if other.is_zero() {
			self
		} else {
			Self(self.0.saturating_sub(other.0) ,self.1)
		}
	}

	/// Addition. Simply tries to unify the denominators and add the numerators.
	///
	/// Overflow might happen during any of the steps. Error is returned in such cases.
	pub fn checked_add(self, other: Self) -> Result<Self, &'static str> {
		let lcm = self.lcm(&other)?;
		let self_scaled = self.to_den(lcm)?;
		let other_scaled = other.to_den(lcm)?;
		let n = self_scaled.0.checked_add(other_scaled.0)
			.ok_or("overflow while adding numerators")?;
		Ok(Self(n, self_scaled.1))
	}

	/// Subtraction. Simply tries to unify the denominators and subtract the numerators.
	///
	/// Overflow might happen during any of the steps. None is returned in such cases.
	pub fn checked_sub(self, other: Self) -> Result<Self, &'static str> {
		let lcm = self.lcm(&other)?;
		let self_scaled = self.to_den(lcm)?;
		let other_scaled = other.to_den(lcm)?;

		let n = self_scaled.0.checked_sub(other_scaled.0)
			.ok_or("overflow while subtracting numerators")?;
		Ok(Self(n, self_scaled.1))
	}
}

impl PartialOrd for Rational128 {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

/// Note that this implementation can very well be lossy. TODO #3670
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
			// general lossy case
			let saturated_lcm = helpers_128bit::multiply_by_rational_best_effort(
				self.1,
				other.1,
				helpers_128bit::gcd(self.1, other.1)
			);
			let self_scaled = self.to_den(saturated_lcm)
				.unwrap_or(Self(Bounded::max_value(), self.1));
			let other_scaled = other.to_den(saturated_lcm)
				.unwrap_or(Self(Bounded::max_value(), other.1));
			self_scaled.n().cmp(&other_scaled.n())
		}
	}
}

/// Note that this implementation can very well be lossy. TODO #3670
impl PartialEq for Rational128 {
    fn eq(&self, other: &Self) -> bool {
		// handle some edge cases.
		if self.1 == other.1 {
			self.0.eq(&other.0)
		} else {
			// general lossy case
			let saturated_lcm = helpers_128bit::multiply_by_rational_best_effort(
				self.1,
				other.1,
				helpers_128bit::gcd(self.1, other.1)
			);
			let self_scaled = self.to_den(saturated_lcm)
				.unwrap_or(Self(Bounded::max_value(), self.1));
			let other_scaled = other.to_den(saturated_lcm)
				.unwrap_or(Self(Bounded::max_value(), other.1));
			self_scaled.n().eq(&other_scaled.n())
		}
    }
}


#[cfg(test)]
mod test_rational128 {
	use super::*;
	use super::helpers_128bit::*;
	use crate::assert_eq_error_rate;
	use rand::Rng;

	const MAX128: u128 = u128::max_value();
	const MAX64: u128 = u64::max_value() as u128;
	const MAX64_2: u128 = 2 * u64::max_value() as u128;

	fn r(p: u128, q: u128) -> Rational128 {
		Rational128(p, q)
	}

	fn mul_div(a: u128, b: u128, c: u128) -> u128 {
		use primitive_types::U256;
		if a.is_zero() { return Zero::zero(); }
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
		assert_eq!(
			mul_div(2u128.pow(100), 8, 4),
			2u128.pow(101)
		);
		assert_eq!(
			mul_div(2u128.pow(100), 4, 8),
			2u128.pow(99)
		);

		// and it returns a if result cannot fit
		assert_eq!(mul_div(MAX128 - 10, 2, 1), MAX128 - 10);
	}

	#[test]
	fn to_denom_works() {
		// simple up and down
		assert_eq!(r(1, 5).to_den(10), Ok(r(2, 10)));
		assert_eq!(r(4, 10).to_den(5), Ok(r(2, 5)));

		// up and down with large numbers
		assert_eq!(r(MAX128 - 10, MAX128).to_den(10), Ok(r(9, 10)));
		assert_eq!(r(MAX128 / 2, MAX128).to_den(10), Ok(r(5, 10)));

		// large to perbill. This is very well needed for phragmen.
		assert_eq!(
			r(MAX128 / 2, MAX128).to_den(1000_000_000),
			Ok(r(500_000_000, 1000_000_000))
		);

		// large to large
		assert_eq!(r(MAX128 / 2, MAX128).to_den(MAX128/2), Ok(r(MAX128/4, MAX128/2)));
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
			r(1_000_000_000, MAX128).lcm(&r(7_000_000_000, MAX128-1)),
			Err("can not accurately multiply by rational in this type"),
		);
		assert_eq!(
			r(1_000_000_000, MAX64).lcm(&r(7_000_000_000, MAX64-1)),
			Ok(340282366920938463408034375210639556610),
		);
		assert!(340282366920938463408034375210639556610 < MAX128);
		assert!(340282366920938463408034375210639556610 == MAX64 * (MAX64 - 1));
	}

	#[test]
	fn add_works() {
		// works
		assert_eq!(r(3, 10).checked_add(r(1, 10)).unwrap(), r(2, 5));
		assert_eq!(r(3, 10).checked_add(r(3, 7)).unwrap(), r(51, 70));

		// errors
		assert_eq!(
			r(1, MAX128).checked_add(r(1, MAX128-1)),
			Err("can not accurately multiply by rational in this type"),
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
			r(2, MAX128).checked_sub(r(1, MAX128-1)),
			Err("can not accurately multiply by rational in this type"),
		);
		assert_eq!(
			r(7, MAX128).checked_sub(r(MAX128, MAX128)),
			Err("overflow while subtracting numerators"),
		);
		assert_eq!(
			r(1, 10).checked_sub(r(2,10)),
			Err("overflow while subtracting numerators"),
		);
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

		// computed with swap
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
			multiply_by_rational(MAX128, 11 , 13).unwrap(),
			(MAX128 / 13 * 11) + (8 * 11 / 13),
		);
		assert_eq!(
			// MAX128 % 1000 == 455
			multiply_by_rational(MAX128, 555, 1000).unwrap(),
			(MAX128 / 1000 * 555) + (455 * 555 / 1000),
		);

		assert_eq!(
			multiply_by_rational(2 * MAX64 - 1, MAX64, MAX64).unwrap(),
			2 * MAX64 - 1,
		);
		assert_eq!(
			multiply_by_rational(2 * MAX64 - 1, MAX64 - 1, MAX64).unwrap(),
			2 * MAX64 - 3,
		);


		assert_eq!(
			multiply_by_rational(MAX64 + 100, MAX64_2, MAX64_2 / 2).unwrap(),
			(MAX64 + 100) * 2,
		);
		assert_eq!(
			multiply_by_rational(MAX64 + 100, MAX64_2 / 100, MAX64_2 / 200).unwrap(),
			(MAX64 + 100) * 2,
		);

		// fails to compute. have to use the greedy, lossy version here
		assert!(multiply_by_rational(2u128.pow(66) - 1, 2u128.pow(65) - 1, 2u128.pow(65)).is_err());
		assert!(multiply_by_rational(1_000_000_000, MAX128 / 8, MAX128 / 2).is_err());
	}

	#[test]
	fn multiply_by_rational_a_b_are_interchangeable() {
		assert_eq!(
			multiply_by_rational(10, MAX128, MAX128 / 2),
			Ok(20),
		);
		assert_eq!(
			multiply_by_rational(MAX128, 10, MAX128 / 2),
			Ok(20),
		);
	}

	#[test]
	fn multiply_by_rational_best_effort_works() {
		assert_eq_error_rate!(
			multiply_by_rational_best_effort(MAX64 + 100, MAX64_2, MAX64_2 / 2),
			(MAX64 + 100) * 2,
			10,
		);
		assert_eq_error_rate!(
			multiply_by_rational_best_effort(MAX64 + 100, MAX64_2 * 100, MAX64_2 * 100 / 2),
			(MAX64 + 100) * 2,
			10,
		);
		assert_eq_error_rate!(
			multiply_by_rational_best_effort(2u128.pow(66) - 1, 2u128.pow(65) - 1, 2u128.pow(65)),
			mul_div(2u128.pow(66) - 1, 2u128.pow(65) - 1, 2u128.pow(65)),
			10,
		);
		assert_eq_error_rate!(
			multiply_by_rational_best_effort(1_000_000_000, MAX128 / 8, MAX128 / 2),
			1_000_000_000 / 4,
			10,
		);

		assert_eq!(
			multiply_by_rational_best_effort(MAX128, MAX128 - 1, MAX128),
			MAX128,
		);

		assert_eq!(
			multiply_by_rational_best_effort(MAX64, MAX128 / 2, MAX128),
			MAX64 / 2,
		);
	}

	fn do_fuzz_multiply_by_rational<F>(
		iters: usize,
		bits: u32,
		maximum_error: u128,
		do_print: bool,
		bounded: bool,
		mul_fn: F,
	) where F: Fn(u128, u128, u128) -> u128 {
		let mut rng = rand::thread_rng();
		let mut average_diff = 0.0;
		let upper_bound = 2u128.pow(bits);

		for _ in 0..iters {
			let a = rng.gen_range(0u128, upper_bound);
			let c = rng.gen_range(0u128, upper_bound);
			let b = rng.gen_range(
				0u128,
				if bounded { c } else { upper_bound }
			);

			let a: u128 = a.into();
			let b: u128 = b.into();
			let c: u128 = c.into();

			let truth = mul_div(a, b, c);
			let result = mul_fn(a, b, c);
			let diff = truth.max(result) - truth.min(result);
			let loss_ratio = diff as f64 / truth as f64;
			average_diff += loss_ratio;

			if do_print && diff > maximum_error {
				println!("++ Computed with more loss than expected: {} * {} / {}", a, b, c);
				println!("++ Expected {}", truth);
				println!("+++++++ Got {}", result);
			}
		}

		// print report
		println!(
			"## Fuzzed with {} numbers. Average error was {}",
			iters,
			average_diff / (iters as f64),
		);
	}

	#[test]
	fn fuzz_multiply_by_rational_best_effort_32() {
		let f = |a, b, c| multiply_by_rational_best_effort(a, b, c);
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 32, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 32, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_best_effort_64() {
		let f = |a, b, c| multiply_by_rational_best_effort(a, b, c);
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 64, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 64, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_best_effort_96() {
		let f = |a, b, c| multiply_by_rational_best_effort(a, b, c);
		// println!("\nInvariant: b < c");
		// do_fuzz_multiply_by_rational(1_000_000, 96, 0, false, true, f);
		println!("every possibility");
		// do_fuzz_multiply_by_rational(1_000_000, 96, 0, false, false, f);
		do_fuzz_multiply_by_rational(10, 96, 0, true, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_best_effort_128() {
		let f = |a, b, c| multiply_by_rational_best_effort(a, b, c);
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 127, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 127, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_32() {
		// if Err just return the truth value. We don't care about such cases. The point of this
		// fuzzing is to make sure: if `multiply_by_rational` returns `Ok`, it must be 100% accurate
		// returning `Err` is fine.
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 32, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 32, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_64() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 64, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 64, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_96() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 96, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 96, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_128() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(1_000_000, 127, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(1_000_000, 127, 0, false, false, f);
	}
}


#[cfg(test)]
mod tests_fixed64 {
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
