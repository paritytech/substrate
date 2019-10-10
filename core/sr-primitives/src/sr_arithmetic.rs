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
	ops, cmp::Ordering, prelude::*,
	convert::{TryFrom, TryInto},
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

/// Infinite precision unsigned integer for substrate runtime.
pub mod biguint {
	use super::Zero;
	use rstd::{cmp::Ordering, ops, prelude::*, cell::RefCell, convert::TryFrom};

	// A sensible value for this would be half of the dword size of the host machine. Since the
	// runtime is compiled to 32bit webassembly, using 32 and 64 for single and double respectively
	// should yield the most performance. TODO #3745 we could benchmark this and verify.
	/// Representation of a single limb.
	pub type Single = u32;
	/// Representation of two limbs.
	pub type Double = u64;
	/// Difference in the number of bits of [`Single`] and [`Double`].
	const SHIFT: usize = 32;
	/// short form of _Base_. Analogous to the value 10 in base-10 decimal numbers.
	const B: Double = Single::max_value() as Double + 1;

	/// Splits a [`Double`] limb number into a tuple of two [`Single`] limb numbers.
	pub fn split(a: Double) -> (Single, Single) {
		let al = a as Single;
		let ah = (a >> SHIFT) as Single;
		(ah, al)
	}

	/// Assumed as a given primitive.
	///
	/// Multiplication of two singles, which at most yields 1 double.
	pub fn mul_single(a: Single, b: Single) -> Double {
		let a: Double = a.into();
		let b: Double = b.into();
		let r = a * b;
		r
	}

	/// Assumed as a given primitive.
	///
	/// Addition of two singles, which at most takes a single limb of result and a carry,
	/// returned as a tuple respectively.
	pub fn add_single(a: Single, b: Single) -> (Single, Single) {
		let a: Double = a.into();
		let b: Double = b.into();
		let q = a + b;
		let (carry, r) = split(q);
		(r, carry)
	}

	/// Assumed as a given primitive.
	///
	/// Division of double by a single limb. Always returns a double limb of quotient and a single
	/// limb of remainder.
	fn div_single(a: Double, b: Single) -> (Double, Single) {
		let b: Double = b.into();
		let q = a / b;
		let r = a % b;
		// both conversions are trivially safe.
		(q, r as Single)
	}

	/// Simple wrapper around an infinitely large integer, represented as limbs of [`Single`].
	#[derive(Clone, Default)]
	pub struct BigUint {
		/// digits (limbs) of this number (sorted as msb -> lsd).
		pub(crate) digits: Vec<Single>,
	}

	impl BigUint {
		/// Create a new instance with `size` limbs. This prevents any number with zero limbs to be
		/// created.
		///
		/// The behavior of the type is undefined with zero limbs.
		pub fn with_capacity(size: usize) -> Self {
			Self { digits: vec![0; size.max(1)] }
		}

		/// Raw constructor from custom limbs. If `limbs` is empty, `Zero::zero()` implementation is
		/// used.
		pub fn from_limbs(limbs: &[Single]) -> Self {
			if limbs.len() > 0 {
				Self { digits: limbs.to_vec() }
			} else {
				Zero::zero()
			}
		}

		/// Number of limbs.
		pub fn len(&self) -> usize { self.digits.len() }

		/// A naive getter for limb at `index`. Note that the order is lsb -> msb.
		///
		/// #### Panics
		///
		/// This panics if index is out of range.
		pub fn get(&self, index: usize) -> Single {
			self.digits[self.len() - 1 - index]
		}

		/// A naive getter for limb at `index`. Note that the order is lsb -> msb.
		pub fn checked_get(&self, index: usize) -> Option<Single> {
			if let Some(i) = self.len().checked_sub(1) {
				if let Some(j) = i.checked_sub(index) {
					return self.digits.get(j).cloned();
				}
			}
			return None;
		}

		/// A naive setter for limb at `index`. Note that the order is lsb -> msb.
		///
		/// #### Panics
		///
		/// This panics if index is out of range.
		pub fn set(&mut self, index: usize, value: Single) {
			let len = self.digits.len();
			self.digits[len - 1 - index] = value;
		}

		/// returns the least significant limb of the number.
		///
		/// #### Panics
		///
		/// While the constructor of the type prevents this, this can panic if `self` has no digits.
		pub fn lsb(&self) -> Single {
			self.digits[self.len() - 1]
		}

		/// returns the most significant limb of the number.
		///
		/// #### Panics
		///
		/// While the constructor of the type prevents this, this can panic if `self` has no digits.
		pub fn msb(&self) -> Single {
			self.digits[0]
		}

		/// Strips zeros from the left side of `self`, if any.
		pub fn lstrip(&mut self) {
			// by definition, a big-int number should never have leading zero limbs. This function
			// has the ability to cause this. There is nothing to do if the number already has 1
			// limb only. call it a day and return.
			if self.len().is_zero() { return; }
			let mut index = 0;
			for elem in self.digits.iter() {
				if *elem != 0 { break } else { index += 1 }
			}
			if index > 0 {
				self.digits = self.digits[index..].to_vec()
			}
		}

		/// Zero-pad `self` from left to reach `size` limbs. Will not make any difference if `self`
		/// is already bigger than `size` limbs.
		pub fn lpad(&mut self, size: usize) {
			let n = self.len();
			if n >= size { return; }
			let pad = size - n;
			let mut new_digits = (0..pad).map(|_| 0).collect::<Vec<Single>>();
			new_digits.extend(self.digits.iter());
			self.digits = new_digits;
		}

		/// Adds `self` with `other`. self and other do not have to have any particular size. Given
		/// that the `n = max{size(self), size(other)}`, it will produce a number with `n + 1`
		/// limbs.
		///
		/// This function does not strip the output and returns the original allocated `n + 1`
		/// limbs. The caller may strip the output if desired.
		///
		/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
		pub fn add(self, other: &Self) -> Self {
			let n = self.len().max(other.len());
			let mut k: Double = 0;
			let mut w = Self::with_capacity(n + 1);

			for j in 0..n {
				let u = Double::from(self.checked_get(j).unwrap_or(0));
				let v = Double::from(other.checked_get(j).unwrap_or(0));
				let s = u + v + k;
				w.set(j, (s % B) as Single);
				k = s / B;
			}
			// k is always 0 or 1.
			w.set(n, k as Single);
			w
		}

		/// Subtracts `other` from `self`. self and other do not have to have any particular size.
		/// Given that the `n = max{size(self), size(other)}`, it will produce a number of size `n`.
		///
		/// If `other` is bigger than `self`, `Err(B - borrow)` is returned.
		///
		/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
		pub fn sub(self, other: &Self) -> Result<Self, Self> {
			let n = self.len().max(other.len());
			let mut k = 0;
			let mut w = Self::with_capacity(n);
			for j in 0..n {
				let s = {
					let u = Double::from(self.checked_get(j).unwrap_or(0));
					let v = Double::from(other.checked_get(j).unwrap_or(0));
					let mut needs_borrow = false;
					let mut t = 0;

					if let Some(v) = u.checked_sub(v) {
						if let Some(v2) = v.checked_sub(k) {
							t = v2 % B;
							k = 0;
						} else {
							needs_borrow = true;
						}
					} else {
						needs_borrow = true;
					}
					if needs_borrow {
						t = u + B - v - k;
						k = 1;
					}
					t
				};
				// PROOF: t either comes from `v2 % B`, or from `u + B - v - k`. The former is
				// trivial. The latter will not overflow this branch will only happen if the sum of
				// `u - v - k` part has been negative, hence `u + B - v - k < b`.
				w.set(j, s as Single);
			}

			if k.is_zero() {
				Ok(w)
			} else {
				Err(w)
			}
		}

		/// Multiplies n-limb number `self` with m-limb number `other`.
		///
		/// The resulting number will always have `n + m` limbs.
		///
		/// This function does not strip the output and returns the original allocated `n + m`
		/// limbs. The caller may strip the output if desired.
		///
		/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
		pub fn mul(self, other: &Self) -> Self {
			let n = self.len();
			let m = other.len();
			let mut w = Self::with_capacity(m + n);

			for j in 0..n {
				if self.get(j) == 0 {
					// Note: `with_capacity` allocates with 0. Explicitly set j + m to zero if
					// otherwise.
					continue;
				}

				let mut k = 0;
				for i in 0..m {
					// PROOF: (B−1) × (B−1) + (B−1) + (B−1) = B^2 −1 < B^2. addition is safe.
					let t =
						mul_single(self.get(j), other.get(i))
						+ Double::from(w.get(i + j))
						+ Double::from(k);
					w.set(i + j, (t % B) as Single);
					// PROOF: (B^2 - 1) / B < B. conversion is safe.
					k = (t / B) as Single;
				}
				w.set(j + m, k);
			}
			w
		}

		/// Divides `self` by a single limb `other`. This can be used in cases where the original
		/// division cannot work due to the divisor (`other`) being just one limb.
		///
		/// Invariant: `other` cannot be zero.
		pub fn div_unit(self, mut other: Single) -> Self {
			other = other.max(1);
			let n = self.len();
			let mut out = Self::with_capacity(n);
			let mut r: Single = 0;
			// PROOF: (B-1) * B + (B-1) still fits in double
			let with_r = |x: Double, r: Single| { r as Double * B + x };
			for d in (0..=n-1).rev() {
				let (q, rr) = div_single(with_r(self.get(d).into(), r), other) ;
				out.set(d, q as Single);
				r = rr;
			}
			out
		}

		/// Divides an `n + m` limb self by a `n` limb `other`. The result is a `m + 1` limb
		/// quotient and a `n` limb remainder, if enabled by passing `true` in `rem` argument, both
		/// in the form of an option's `Ok`.
		///
		/// - requires `other` to be stripped and have no leading zeros.
		/// - requires `self` to be stripped and have no leading zeros.
		/// - requires `other` to have at least two limbs.
		/// - requires `self` to have a greater length compared to `other`.
		///
		/// All arguments are examined without being stripped for the above conditions. If any of
		/// the above fails, `None` is returned.`
		///
		/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
		pub fn div(self, other: &Self, rem: bool) -> Option<(Self, Self)> {
			if other.len() <= 1
				|| other.msb() == 0
				|| self.msb() == 0
				|| self.len() <= other.len()
			{
				return None
			}
			let n = other.len();
			let m = self.len() - n;

			let mut q = Self::with_capacity(m + 1);
			let mut r = Self::with_capacity(n);

			debug_assert!(other.msb() != 0);

			// PROOF: 0 <= normalizer_bits < SHIFT 0 <= normalizer < B. all conversions are
			// safe.
			let normalizer_bits = other.msb().leading_zeros() as Single;
			let normalizer = (2 as Single).pow(normalizer_bits as u32) as Single;

			// step D1.
			let mut self_norm = self.mul(&Self::from(normalizer));
			let mut other_norm = other.clone().mul(&Self::from(normalizer));

			// defensive only; the mul implementation should always create this.
			self_norm.lpad(n + m + 1);
			other_norm.lstrip();

			// step D2.
			for j in (0..=m).rev() {
				// step D3.0 Find an estimate of q[j], named qhat.
				let (qhat, rhat) = {
					// PROOF: this always fits into `Double`. In the context of Single = u8, and
					// Double = u16, think of 255 * 256 + 255 which is just u16::max_value().
					let dividend =
						Double::from(self_norm.get(j + n))
						* B
						+ Double::from(self_norm.get(j + n - 1));
					let divisor = other_norm.get(n - 1);
					div_single(dividend, divisor.into())
				};

				// D3.1 test qhat
				// replace qhat and rhat with RefCells. This helps share state with the closure
				let qhat = RefCell::new(qhat);
				let rhat = RefCell::new(rhat as Double);

				let test = || {
					// decrease qhat if it is bigger than the base (B)
					let qhat_local = *qhat.borrow();
					let rhat_local = *rhat.borrow();
					let predicate_1 = qhat_local >= B;
					let predicate_2 = {
						let lhs = qhat_local * other_norm.get(n - 2) as Double;
						let rhs = B * rhat_local + self_norm.get(j + n - 2) as Double;
						lhs > rhs
					};
					if predicate_1 || predicate_2 {
						*qhat.borrow_mut() -= 1;
						*rhat.borrow_mut() += other_norm.get(n - 1) as Double;
						true
					} else {
						false
					}
				};

				test();
				while (*rhat.borrow() as Double) < B {
					if !test() { break; }
				}

				let qhat = qhat.into_inner();
				// we don't need rhat anymore. just let it go out of scope when it does.

				// step D4
				let lhs = Self { digits: (j..=j+n).rev().map(|d| self_norm.get(d)).collect() };
				let rhs = other_norm.clone().mul(&Self::from(qhat));

				let maybe_sub = lhs.sub(&rhs);
				let mut negative = false;
				let sub = match maybe_sub {
					Ok(t) => t,
					Err(t) => { negative = true; t }
				};
				(j..=j+n).for_each(|d| { self_norm.set(d, sub.get(d - j)); });

				// step D5
				// PROOF: the `test()` specifically decreases qhat until it is below `B`. conversion
				// is safe.
				q.set(j, qhat as Single);

				// step D6: add back if negative happened.
				if negative {
					q.set(j, q.get(j) - 1);
					let u = Self { digits: (j..=j+n).rev().map(|d| self_norm.get(d)).collect() };
					let r = other_norm.clone().add(&u);
					(j..=j+n).rev().for_each(|d| { self_norm.set(d, r.get(d - j)); })
				}
			}

			// if requested, calculate remainder.
			if rem {
				// undo the normalization.
				if normalizer_bits > 0 {
					let s = SHIFT as u32;
					let nb = normalizer_bits;
					for d in 0..n-1 {
						let v = self_norm.get(d) >> nb
							| self_norm.get(d + 1).overflowing_shl(s - nb).0;
						r.set(d, v);
					}
					r.set(n - 1, self_norm.get(n - 1) >> normalizer_bits);
				} else {
					r = self_norm;
				}
			}

			Some((q, r))
		}
	}

	#[cfg(feature = "std")]
	impl rstd::fmt::Debug for BigUint {
		fn fmt(&self, f: &mut rstd::fmt::Formatter<'_>) -> rstd::fmt::Result {
			write!(
				f,
				"BigUint {{ {:?} ({:?})}}",
				self.digits,
				u128::try_from(self.clone()).unwrap_or_else(|_| 0),
			)
		}
	}

	impl PartialEq for BigUint {
		fn eq(&self, other: &Self) -> bool {
			// sadly, we have to reallocate here as strip mutably uses self.
			let mut lhs = self.clone();
			let mut rhs = other.clone();
			lhs.lstrip();
			rhs.lstrip();
			lhs.digits.eq(&rhs.digits)
		}
	}

	impl Eq for BigUint {}

	impl Ord for BigUint {
		fn cmp(&self, other: &Self) -> Ordering {
			let lhs_first = self.digits.iter().position(|&e| e != 0);
			let rhs_first = other.digits.iter().position(|&e| e != 0);

			match (lhs_first, rhs_first) {
				// edge cases that should not happen. This basically means that one or both were
				// zero.
				(None, None) => Ordering::Equal,
				(Some(_), None) => Ordering::Greater,
				(None, Some(_)) => Ordering::Less,
				(Some(lhs_idx), Some(rhs_idx)) => {
					let lhs = &self.digits[lhs_idx..];
					let rhs = &other.digits[rhs_idx..];
					let len_cmp = lhs.len().cmp(&rhs.len());
					match len_cmp {
						Ordering::Equal => lhs.cmp(rhs),
						_ => len_cmp,
					}
				}
			}
		}
	}

	impl PartialOrd for BigUint {
		fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
			Some(self.cmp(other))
		}
	}

	impl ops::Add for BigUint {
		type Output = Self;
		fn add(self, rhs: Self) -> Self::Output {
			self.add(&rhs)
		}
	}

	impl ops::Sub for BigUint {
		type Output = Self;
		fn sub(self, rhs: Self) -> Self::Output {
			self.sub(&rhs).unwrap_or_else(|e| e)
		}
	}

	impl ops::Mul for BigUint {
		type Output = Self;
		fn mul(self, rhs: Self) -> Self::Output {
			self.mul(&rhs)
		}
	}

	impl Zero for BigUint {
		fn zero() -> Self {
			Self { digits: vec![Zero::zero()] }
		}

		fn is_zero(&self) -> bool {
			self.digits.iter().all(|d| d.is_zero())
		}
	}

	macro_rules! impl_try_from_number_for {
		($([$type:ty, $len:expr]),+) => {
			$(
				impl TryFrom<BigUint> for $type {
					type Error = &'static str;
					fn try_from(mut value: BigUint) -> Result<$type, Self::Error> {
						value.lstrip();
						let error_message = concat!("cannot fit a number into ", stringify!($type));
						if value.len() * SHIFT > $len {
							Err(error_message)
						} else {
							let mut acc: $type = Zero::zero();
							for (i, d) in value.digits.iter().rev().cloned().enumerate() {
								let d: $type = d.into();
								acc += d << (SHIFT * i);
							}
							Ok(acc)
						}
					}
				}
			)*
		};
	}
	// can only be implemented for sizes bigger than two limb.
	impl_try_from_number_for!([u128, 128], [u64, 64]);

	macro_rules! impl_from_for_smaller_than_word {
		($($type:ty),+) => {
			$(impl From<$type> for BigUint {
				fn from(a: $type) -> Self {
					Self { digits: vec! [a.into()] }
				}
			})*
		}
	}
	impl_from_for_smaller_than_word!(u8, u16, Single);

	impl From<Double> for BigUint {
		fn from(a: Double) -> Self {
			let (ah, al) = split(a);
			Self { digits: vec![ah, al] }
		}
	}

	#[cfg(test)]
	pub mod tests_biguint {
		use super::*;
		use rand::Rng;
		#[cfg(feature = "bench")]
		use test::Bencher;

		// TODO move into a proper fuzzer #3745
		const FUZZ_COUNT: usize = 100_000;

		pub fn random_big_uint(size: usize) -> BigUint {
			let mut rng = rand::thread_rng();
			let digits = (0..size).map(|_| rng.gen_range(0, Single::max_value())).collect();
			BigUint { digits }
		}

		fn run_with_data_set<F>(
			count: usize,
			limbs_ub_1: usize,
			limbs_ub_2: usize,
			exact: bool,
			assertion: F,
		) where
			F: Fn(BigUint, BigUint) -> ()
		{
			let mut rng = rand::thread_rng();
			for _ in 0..count {
				let digits_len_1 = if exact { limbs_ub_1 } else { rng.gen_range(1, limbs_ub_1) };
				let digits_len_2 = if exact { limbs_ub_2 } else { rng.gen_range(1, limbs_ub_2) };

				let u = random_big_uint(digits_len_1);
				let v = random_big_uint(digits_len_2);
				assertion(u, v);
			}
		}

		fn with_limbs(n: usize) -> BigUint {
			BigUint { digits: vec![1; n] }
		}

		#[test]
		fn split_works() {
			let a = SHIFT / 2;
			let b = SHIFT * 3 / 2;
			let num: Double = 1 << a | 1 << b;
			// example when `Single = u8`
			// assert_eq!(num, 0b_0001_0000_0001_0000)
			assert_eq!(split(num), (1 << a, 1 << a));
		}

		#[test]
		fn strip_works() {
			let mut a = BigUint::from_limbs(&[0, 1, 0]);
			a.lstrip();
			assert_eq!(a, BigUint { digits: vec![1, 0] });

			let mut a = BigUint::from_limbs(&[0, 0, 1]);
			a.lstrip();
			assert_eq!(a, BigUint { digits: vec![1] });

			let mut a = BigUint::from_limbs(&[0, 0]);
			a.lstrip();
			assert_eq!(a, BigUint { digits: vec![0] });

			let mut a = BigUint::from_limbs(&[0, 0, 0]);
			a.lstrip();
			assert_eq!(a, BigUint { digits: vec![0] });
		}

		#[test]
		fn lpad_works() {
			let mut a = BigUint::from_limbs(&[0, 1, 0]);
			a.lpad(2);
			assert_eq!(a.digits, vec![0, 1, 0]);

			let mut a = BigUint::from_limbs(&[0, 1, 0]);
			a.lpad(3);
			assert_eq!(a.digits, vec![0, 1, 0]);

			let mut a = BigUint::from_limbs(&[0, 1, 0]);
			a.lpad(4);
			assert_eq!(a.digits, vec![0, 0, 1, 0]);
		}

		#[test]
		fn equality_works() {
			assert_eq!(
				BigUint { digits: vec![1, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
				true,
			);
			assert_eq!(
				BigUint { digits: vec![3, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
				false,
			);
			assert_eq!(
				BigUint { digits: vec![0, 1, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
				true,
			);
		}

		#[test]
		fn ordering_works() {
			assert!(BigUint { digits: vec![0] } < BigUint { digits: vec![1] });
			assert!(BigUint { digits: vec![0] } == BigUint { digits: vec![0] });
			assert!(BigUint { digits: vec![] } == BigUint { digits: vec![0] });
			assert!(BigUint { digits: vec![] } == BigUint { digits: vec![] });
			assert!(BigUint { digits: vec![] } < BigUint { digits: vec![1] });

			assert!(BigUint { digits: vec![1, 2, 3] } == BigUint { digits: vec![1, 2, 3] });
			assert!(BigUint { digits: vec![0, 1, 2, 3] } == BigUint { digits: vec![1, 2, 3] });

			assert!(BigUint { digits: vec![1, 2, 4] } > BigUint { digits: vec![1, 2, 3] });
			assert!(BigUint { digits: vec![0, 1, 2, 4] } > BigUint { digits: vec![1, 2, 3] });
			assert!(BigUint { digits: vec![1, 2, 1, 0] } > BigUint { digits: vec![1, 2, 3] });

			assert!(BigUint { digits: vec![0, 1, 2, 1] } < BigUint { digits: vec![1, 2, 3] });
		}

		#[test]
		fn basic_random_ord_eq_works() {
			type S = u128;
			run_with_data_set(FUZZ_COUNT, 4, 4, false, |u, v| {
				let ue = S::try_from(u.clone()).unwrap();
				let ve = S::try_from(v.clone()).unwrap();
				assert_eq!(u.cmp(&v), ue.cmp(&ve));
				assert_eq!(u.eq(&v), ue.eq(&ve));
			})
		}

		#[test]
		fn can_try_build_numbers_from_types() {
			use rstd::convert::TryFrom;
			assert_eq!(u64::try_from(with_limbs(1)).unwrap(), 1);
			assert_eq!(u64::try_from(with_limbs(2)).unwrap(), u32::max_value() as u64 + 2);
			assert_eq!(
				u64::try_from(with_limbs(3)).unwrap_err(),
				"cannot fit a number into u64",
			);
			assert_eq!(
				u128::try_from(with_limbs(3)).unwrap(),
				u32::max_value() as u128 + u64::max_value() as u128 + 3
			);
		}

		#[test]
		fn zero_works() {
			assert_eq!(BigUint::zero(), BigUint { digits: vec![0] });
			assert_eq!(BigUint { digits: vec![0, 1, 0] }.is_zero(), false);
			assert_eq!(BigUint { digits: vec![0, 0, 0] }.is_zero(), true);

			let a = BigUint::zero();
			let b = BigUint::zero();
			let c = a * b;
			assert_eq!(c.digits, vec![0, 0]);
		}

		#[test]
		fn basic_random_add_works() {
			type S = u128;
			run_with_data_set(FUZZ_COUNT, 3, 3, false, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() + S::try_from(v.clone()).unwrap();
				let t = u.clone().add(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} + {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			})
		}

		#[test]
		fn sub_negative_works() {
			assert_eq!(
				BigUint::from(10 as Single).sub(&BigUint::from(5 as Single)).unwrap(),
				BigUint::from(5 as Single)
			);
			assert_eq!(
				BigUint::from(10 as Single).sub(&BigUint::from(10 as Single)).unwrap(),
				BigUint::from(0 as Single)
			);
			assert_eq!(
				BigUint::from(10 as Single).sub(&BigUint::from(13 as Single)).unwrap_err(),
				BigUint::from((B - 3) as Single),
			);
		}

		#[test]
		fn basic_random_sub_works() {
			type S = u128;
			run_with_data_set(FUZZ_COUNT, 4, 4, false, |u, v| {
				let expected = S::try_from(u.clone()).unwrap()
					.checked_sub(S::try_from(v.clone()).unwrap());
				let t = u.clone().sub(&v);
				if expected.is_none() {
					assert!(t.is_err())
				} else {
					let t = t.unwrap();
					let expected = expected.unwrap();
					assert_eq!(
						S::try_from(t.clone()).unwrap(), expected,
						"{:?} - {:?} ===> {:?} != {:?}", u, v, t, expected,
					);
				}
			})
		}

		#[test]
		fn basic_random_mul_works() {
			type S = u128;
			run_with_data_set(FUZZ_COUNT, 2, 2, false, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() * S::try_from(v.clone()).unwrap();
				let t = u.clone().mul(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} * {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			})
		}

		#[test]
		fn mul_always_appends_one_digit() {
			let a = BigUint::from(10 as Single);
			let b = BigUint::from(4 as Single);
			assert_eq!(a.len(), 1);
			assert_eq!(b.len(), 1);

			let n = a.mul(&b);

			assert_eq!(n.len(), 2);
			assert_eq!(n.digits, vec![0, 40]);
		}

		#[test]
		fn div_conditions_work() {
			let a = BigUint { digits: vec![2] };
			let b = BigUint { digits: vec![1, 2] };
			let c = BigUint { digits: vec![1, 1, 2] };
			let d = BigUint { digits: vec![0, 2] };
			let e = BigUint { digits: vec![0, 1, 1, 2] };

			assert!(a.clone().div(&b, true).is_none());
			assert!(c.clone().div(&a, true).is_none());
			assert!(c.clone().div(&d, true).is_none());
			assert!(e.clone().div(&a, true).is_none());

			assert!(c.clone().div(&b, true).is_some());
		}

		#[test]
		fn div_unit_works() {
			let a = BigUint { digits: vec![100] };
			let b = BigUint { digits: vec![1, 100] };

			assert_eq!(a.clone().div_unit(1), a);
			assert_eq!(a.clone().div_unit(0), a);
			assert_eq!(a.clone().div_unit(2), BigUint::from(50 as Single));
			assert_eq!(a.clone().div_unit(7), BigUint::from(14 as Single));

			assert_eq!(b.clone().div_unit(1), b);
			assert_eq!(b.clone().div_unit(0), b);
			assert_eq!(b.clone().div_unit(2), BigUint::from(((B + 100) / 2) as Single));
			assert_eq!(b.clone().div_unit(7), BigUint::from(((B + 100) / 7) as Single));

		}

		#[test]
		fn basic_random_div_works() {
			type S = u128;
			run_with_data_set(FUZZ_COUNT, 4, 4, false, |u, v| {
				let ue = S::try_from(u.clone()).unwrap();
				let ve = S::try_from(v.clone()).unwrap();
				let (q, r) = (ue / ve, ue % ve);
				if let Some((qq, rr)) = u.clone().div(&v, true) {
					assert_eq!(
						S::try_from(qq.clone()).unwrap(), q,
						"{:?} / {:?} ===> {:?} != {:?}", u, v, qq, q,
					);
					assert_eq!(
						S::try_from(rr.clone()).unwrap(), r,
						"{:?} % {:?} ===> {:?} != {:?}", u, v, rr, r,
					);
				} else if v.len() == 1 {
					let qq = u.clone().div_unit(ve as Single);
					assert_eq!(
						S::try_from(qq.clone()).unwrap(), q,
						"[single] {:?} / {:?} ===> {:?} != {:?}", u, v, qq, q,
					);
				} else {
					if v.msb() == 0 || v.msb() == 0 || u.len() <= v.len() {} // nada
					else { panic!("div returned none for an unexpected reason"); }
				}
			})
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_addition_2_digit(bencher: &mut Bencher) {
			let a = random_big_uint(2);
			let b = random_big_uint(2);
			bencher.iter(|| {
				let _ = a.clone().add(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_addition_4_digit(bencher: &mut Bencher) {
			let a = random_big_uint(4);
			let b = random_big_uint(4);
			bencher.iter(|| {
				let _ = a.clone().add(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_subtraction_2_digit(bencher: &mut Bencher) {
			let a = random_big_uint(2);
			let b = random_big_uint(2);
			bencher.iter(|| {
				let _ = a.clone().sub(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_subtraction_4_digit(bencher: &mut Bencher) {
			let a = random_big_uint(4);
			let b = random_big_uint(4);
			bencher.iter(|| {
				let _ = a.clone().sub(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_multiplication_2_digit(bencher: &mut Bencher) {
			let a = random_big_uint(2);
			let b = random_big_uint(2);
			bencher.iter(|| {
				let _ = a.clone().mul(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_multiplication_4_digit(bencher: &mut Bencher) {
			let a = random_big_uint(4);
			let b = random_big_uint(4);
			bencher.iter(|| {
				let _ = a.clone().mul(&b);
			});
		}

		#[cfg(feature = "bench")]
		#[bench]
		fn bench_division_4_digit(bencher: &mut Bencher) {
			let a = random_big_uint(4);
			let b = random_big_uint(2);
			bencher.iter(|| {
				let _ = a.clone().div(&b, true);
			});
		}
	}
}

/// Some helper functions to work with 128bit numbers. Note that the functionality provided here is
/// only sensible to use with 128bit numbers because for smaller sizes, you can always rely on
/// assumptions of a bigger type (u128) being available, or simply create a per-thing and use the
/// multiplication implementation provided there.
pub mod helpers_128bit {
	use crate::biguint;
	use crate::traits::Zero;
	use rstd::{cmp::{min, max}, convert::TryInto};

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

	/// split a u128 into two u64 limbs
	pub fn split(a: u128) -> (u64, u64) {
		let al = a as u64;
		let ah = (a >> 64) as u64;
		(ah, al)
	}

	/// Convert a u128 to a u32 based biguint.
	pub fn to_big_uint(x: u128) -> biguint::BigUint {
		let (xh, xl) = split(x);
		let (xhh, xhl) = biguint::split(xh);
		let (xlh, xll) = biguint::split(xl);
		let mut n = biguint::BigUint::from_limbs(&[xhh, xhl, xlh, xll]);
		n.lstrip();
		n
	}

	/// Safely and accurately compute `a * b / c`. The approach is:
	///   - Simply try `a * b / c`.
	///   - Else, convert them both into big numbers and re-try. `Err` is returned if the result
	///     cannot be safely casted back to u128.
	///
	/// Invariant: c must be greater than or equal to 1.
	pub fn multiply_by_rational(a: u128, b: u128, c: u128) -> Result<u128, &'static str> {
		if a.is_zero() || b.is_zero() { return Ok(Zero::zero()); }
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
		} else {
			let a_num = to_big_uint(a);
			let b_num = to_big_uint(b);
			let c_num = to_big_uint(c);

			let mut ab = a_num * b_num;
			ab.lstrip();
			let mut q = if c_num.len() == 1 {
				// PROOF: if `c_num.len() == 1` then `c` fits in one limb.
				ab.div_unit(c as biguint::Single)
			} else {
				// PROOF: both `ab` and `c` cannot have leading zero limbs; if length of `c` is 1,
				// the previous branch would handle. Also, if ab for sure has a bigger size than
				// c, because `a.checked_mul(b)` has failed, hence ab must be at least one limb
				// bigger than c. In this case, returning zero is defensive-only and div should
				// always return Some.
				let (mut q, r) = ab.div(&c_num, true).unwrap_or((Zero::zero(), Zero::zero()));
				let r: u128 = r.try_into()
					.expect("reminder of div by c is always less than c; qed");
				if r > (c / 2) { q = q.add(&to_big_uint(1)); }
				q
			};
			q.lstrip();
			q.try_into().map_err(|_| "result cannot fit in u128")
		}
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
			 helpers_128bit::multiply_by_rational(self.0, den, self.1).map(|n| Self(n, den))
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
		let lcm = self.lcm(&other).map_err(|_| "failed to scale to denominator")?;
		let self_scaled = self.to_den(lcm).map_err(|_| "failed to scale to denominator")?;
		let other_scaled = other.to_den(lcm).map_err(|_| "failed to scale to denominator")?;
		let n = self_scaled.0.checked_add(other_scaled.0)
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
			let other_n = helpers_128bit::to_big_uint(other.0) * helpers_128bit::to_big_uint(self.1);
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
			let other_n = helpers_128bit::to_big_uint(other.0) * helpers_128bit::to_big_uint(self.1);
			self_n.eq(&other_n)
		}
    }
}

#[cfg(test)]
mod test_rational128 {
	use super::*;
	use super::helpers_128bit::*;
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
		assert_eq!(r(MAX128 - 10, MAX128).to_den(10), Ok(r(10, 10)));
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
			Err("result cannot fit in u128"),
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
			r(2, MAX128).checked_sub(r(1, MAX128-1)),
			Err("failed to scale to denominator"),
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

		assert_eq!(
			multiply_by_rational(2u128.pow(66) - 1, 2u128.pow(65) - 1, 2u128.pow(65)).unwrap(),
			73786976294838206461,
		);
		assert_eq!(
			multiply_by_rational(1_000_000_000, MAX128 / 8, MAX128 / 2).unwrap(),
			250000000,
		);
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

	// TODO $# move into a proper fuzzer #3745
	const FUZZ_COUNT: usize = 100_000;

	#[test]
	fn fuzz_multiply_by_rational_32() {
		// if Err just return the truth value. We don't care about such cases. The point of this
		// fuzzing is to make sure: if `multiply_by_rational` returns `Ok`, it must be 100% accurate
		// returning `Err` is fine.
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 32, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 32, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_64() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 64, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 64, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_96() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 96, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 96, 0, false, false, f);
	}

	#[test]
	fn fuzz_multiply_by_rational_128() {
		let f = |a, b, c| multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c));
		println!("\nInvariant: b < c");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 127, 0, false, true, f);
		println!("every possibility");
		do_fuzz_multiply_by_rational(FUZZ_COUNT, 127, 0, false, false, f);
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
