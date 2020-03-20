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

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};

use sp_std::{ops, prelude::*, convert::TryInto};
use codec::{Encode, Decode, CompactAs};
use crate::traits::{
	SaturatedConversion, UniqueSaturatedFrom, UniqueSaturatedInto, Saturating, BaseArithmetic, Zero,
};
use sp_debug_derive::RuntimeDebug;

/// Something that implements a fixed point ration with an arbitrary granularity `X`, as _parts per
/// `X`_.
pub trait PerThing: Sized + Saturating + Copy {
	/// The data type used to build this per-thingy.
	type Inner: BaseArithmetic + Copy;

	/// A data type larger than `Self::Inner`, used to avoid overflow in some computations.
	/// It must be able to compute `ACCURACY^2`.
	type Upper: BaseArithmetic + Copy + From<Self::Inner> + TryInto<Self::Inner>;

	/// The accuracy of this type.
	const ACCURACY: Self::Inner;

	/// Equivalent to `Self::from_parts(0)`.
	fn zero() -> Self { Self::from_parts(Self::Inner::zero()) }

	/// Return `true` if this is nothing.
	fn is_zero(&self) -> bool { self.deconstruct() == Self::Inner::zero() }

	/// Equivalent to `Self::from_parts(Self::ACCURACY)`.
	fn one() -> Self { Self::from_parts(Self::ACCURACY) }

	/// Return `true` if this is one.
	fn is_one(&self) -> bool { self.deconstruct() == Self::ACCURACY }

	/// Build this type from a percent. Equivalent to `Self::from_parts(x * Self::ACCURACY / 100)`.
	fn from_percent(x: Self::Inner) -> Self {
		Self::from_parts(x.min(100.into()) * (Self::ACCURACY / 100.into()))
	}

	/// Return the product of multiplication of this value by itself.
	fn square(self) -> Self {
		let p = Self::Upper::from(self.deconstruct());
		let q = Self::Upper::from(Self::ACCURACY); 
		Self::from_rational_approximation(p * p, q * q)
	}

	/// Saturating reciprocal multiplication. Compute `x / self`, saturating at the numeric 
	/// bounds instead of overflowing.
	///
	/// If `truncate` is true, round down. Otherwise round to the nearest value of N.
	fn saturating_reciprocal_mul<N>(self, x: N, truncate: bool) -> N
	where N: Clone + From<Self::Inner> + UniqueSaturatedFrom<Self::Upper> + UniqueSaturatedInto<Self::Inner> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> + ops::Rem<N, Output=N> + Saturating {
		let maximum: N = Self::ACCURACY.into();
		let part: N = self.deconstruct().into();
		let c = rational_mul_correction::<N, Self>(
			x.clone(), 
			Self::ACCURACY, 
			self.deconstruct(), 
			truncate,
		);
		(x / part).saturating_mul(maximum).saturating_add(c)
	}

	/// Overflow-prune multiplication. Accurately multiply a value by `self` without overflowing.
	///
	/// If `truncate` is true, round down. Otherwise round to the nearest value of N.
	fn overflow_prune_mul<N>(self, x: N, truncate: bool) -> N 
	where N: Clone + From<Self::Inner> + UniqueSaturatedInto<Self::Inner> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> + ops::Rem<N, Output=N> {
		let maximum: N = Self::ACCURACY.into();
		let part: N = self.deconstruct().into();
		let c = rational_mul_correction::<N, Self>(
			x.clone(), 
			self.deconstruct(), 
			Self::ACCURACY, 
			truncate,
		);
		(x / maximum) * part + c
	}

	/// Consume self and return the number of parts per thing. 
	fn deconstruct(self) -> Self::Inner;

	/// Build this type from a number of parts per thing.
	fn from_parts(parts: Self::Inner) -> Self;

	/// Converts a fraction into `Self`.
	#[cfg(feature = "std")]
	fn from_fraction(x: f64) -> Self;

	/// Approximate the fraction `p/q` into a per-thing fraction. This will never overflow.
	///
	/// The computation of this approximation is performed in the generic type `N`. Given
	/// `M` as the data type that can hold the maximum value of this per-thing (e.g. u32 for
	/// perbill), this can only work if `N == M` or `N: From<M> + TryInto<M>`.
	fn from_rational_approximation<N>(p: N, q: N) -> Self
	where N: Clone + Ord + From<Self::Inner> + TryInto<Self::Inner> + ops::Div<N, Output=N>;
}

/// Compute the error due to integer division in the expression `x / denom * numer`.
///
/// Take the remainder of `x / denom` and multiply by  `numer / denom`. The result can be added
/// to `x / denom * numer` for an accurate result.
fn rational_mul_correction<N, P>(x: N, numer: P::Inner, denom: P::Inner, truncate: bool) -> N
where 
	N: From<P::Inner> + UniqueSaturatedInto<P::Inner> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> + ops::Rem<N, Output=N>,
	P: PerThing,
{
	let numer_upper = P::Upper::from(numer);
	let denom_n = N::from(denom);
	let denom_upper = P::Upper::from(denom);
	let rem = x.rem(denom_n);
	// `rem` is less than `denom`, which fits in `P::Inner`.
	let rem_inner = rem.saturated_into::<P::Inner>();
	// `P::Upper` always fits `P::Inner::max_value().pow(2)`, thus it fits `rem * numer`.
	let rem_mul_upper = P::Upper::from(rem_inner) * numer_upper;
	// `rem` is less than `denom`, so if `numer` is an integer then `rem * numer / denom` is less
	// than `numer`, which fits in `P::Inner`.
	let mut rem_mul_div_inner = (rem_mul_upper / denom_upper).saturated_into::<P::Inner>();
	// Check if the fractional part of the result is closer to 1 than 0. 
	if !truncate && rem_mul_upper % denom_upper > denom_upper / 2.into() {
		// `rem * numer / denom` is less than `numer`, so this will not overflow.
		rem_mul_div_inner = rem_mul_div_inner + 1.into();
	}
	rem_mul_div_inner.into()
}

macro_rules! implement_per_thing {
	($name:ident, $test_mod:ident, [$($test_units:tt),+], $max:tt, $type:ty, $upper_type:ty, $title:expr $(,)?) => {
		/// A fixed point representation of a number in the range [0, 1].
		///
		#[doc = $title]
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
		#[derive(Encode, Decode, Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, RuntimeDebug, CompactAs)]
		pub struct $name($type);

		impl PerThing for $name {
			type Inner = $type;
			type Upper = $upper_type;

			/// The accuracy of this type.
			const ACCURACY: Self::Inner = $max;

			/// Consume self and return the number of parts per thing. 
			fn deconstruct(self) -> Self::Inner { self.0 }

			/// Build this type from a number of parts per thing.
			fn from_parts(parts: Self::Inner) -> Self { Self(parts.min($max)) }

			/// Converts a fraction into `Self`.
			#[cfg(feature = "std")]
			fn from_fraction(x: f64) -> Self { Self((x * ($max as f64)) as Self::Inner) }

			/// Approximate the fraction `p/q` into a per-thing fraction. This will never overflow.
			///
			/// The computation of this approximation is performed in the generic type `N`. Given
			/// `M` as the data type that can hold the maximum value of this per-thing (e.g. u32 for
			/// perbill), this can only work if `N == M` or `N: From<M> + TryInto<M>`.
			fn from_rational_approximation<N>(p: N, q: N) -> Self
			where N: Clone + Ord + From<Self::Inner> + TryInto<Self::Inner> + ops::Div<N, Output=N> {
				// q cannot be zero.
				let q = q.max((1 as Self::Inner).into());
				// p should not be bigger than q.
				let p = p.min(q.clone());

				let factor = (q.clone() / $max.into()).max((1 as Self::Inner).into());

				// q cannot overflow: (q / (q/$max)) < 2 * $max. p < q hence p also cannot overflow.
				// this implies that Self::Inner must be able to fit 2 * $max.
				let q_reduce: Self::Inner = (q / factor.clone())
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"q / (q/$max) < (2 * $max). Macro prevents any type being created that \
						does not satisfy this; qed"
					);
				let p_reduce: Self::Inner = (p / factor.clone())
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"q / (q/$max) < (2 * $max). Macro prevents any type being created that \
						does not satisfy this; qed"
					);

				// `p_reduced` and `q_reduced` are withing Self::Inner. Mul by another $max will
				// always fit in $upper_type. This is guaranteed by the macro tests.
				let part =
					p_reduce as $upper_type
					* <$upper_type>::from($max)
					/ q_reduce as $upper_type;

				$name(part as Self::Inner)
			}
		}

		/// Implement const functions
		impl $name {
			/// From an explicitly defined number of parts per maximum of the type.
			///
			/// This can be called at compile time.
			pub const fn from_parts(parts: $type) -> Self {
				Self([parts, $max][(parts > $max) as usize])
			}

			/// Converts a percent into `Self`. Equal to `x / 100`.
			///
			/// This can be created at compile time.
			pub const fn from_percent(x: $type) -> Self {
				Self([x, 100][(x > 100) as usize] * ($max / 100))
			}

			/// Everything.
			///
			/// To avoid having to import `PerThing` when one needs to be used in test mocks.
			#[cfg(feature = "std")]
			pub fn one() -> Self {
				<Self as PerThing>::one()
			}
		}

		impl Saturating for $name {
			/// Saturating addition. Compute `self + rhs`, saturating at the numeric bounds instead of
			/// overflowing. This operation is lossless if it does not saturate.
			fn saturating_add(self, rhs: Self) -> Self {
				// defensive-only: since `$max * 2 < $type::max_value()`, this can never overflow.
				Self::from_parts(self.0.saturating_add(rhs.0))
			}

			/// Saturating subtraction. Compute `self - rhs`, saturating at the numeric bounds instead of
			/// overflowing. This operation is lossless if it does not saturate.
			fn saturating_sub(self, rhs: Self) -> Self {
				Self::from_parts(self.0.saturating_sub(rhs.0))
			}

			/// Saturating multiply. Compute `self * rhs`, saturating at the numeric bounds instead of
			/// overflowing. This operation is lossy.
			fn saturating_mul(self, rhs: Self) -> Self {
				let a = self.0 as $upper_type;
				let b = rhs.0 as $upper_type;
				let m = <$upper_type>::from($max);
				let parts = a * b / m;
				// This will always fit into $type.
				Self::from_parts(parts as $type)
			}

			/// Saturating exponentiation. Computes `self.pow(exp)`, saturating at the numeric
			/// bounds instead of overflowing. This operation is lossy.
			fn saturating_pow(self, exp: usize) -> Self {
				if self.is_zero() || self.is_one() {
					self
				} else {
					let p = <$name as PerThing>::Upper::from(self.deconstruct());
					let q = <$name as PerThing>::Upper::from(Self::ACCURACY);
					let mut s = Self::one();
					for _ in 0..exp {
						if s.is_zero() {
							break;
						} else {
							// x^2 always fits in Self::Upper if x fits in Self::Inner.
							// Verified by a test.
							s = Self::from_rational_approximation(
								<$name as PerThing>::Upper::from(s.deconstruct()) * p, 
								q * q,
							);
						}
					}
					s
				}
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
				self.overflow_prune_mul(b, false)
			}
		}

		#[cfg(test)]
		mod $test_mod {
			use codec::{Encode, Decode};
			use super::{$name, Saturating, RuntimeDebug, PerThing};
			use crate::traits::Zero;


			#[test]
			fn macro_expanded_correctly() {
				// needed for the `from_percent` to work.
				assert!($max >= 100);
				assert!($max % 100 == 0);

				// needed for `from_rational_approximation`
				assert!(2 * $max < <$type>::max_value());
				assert!(<$upper_type>::from($max) < <$upper_type>::max_value());

				// for something like percent they can be the same.
				assert!((<$type>::max_value() as $upper_type) <= <$upper_type>::max_value());
				assert!(<$upper_type>::from($max).checked_mul($max.into()).is_some());

				// make sure saturating_pow won't overflow the upper type
				assert!(<$upper_type>::from($max) * <$upper_type>::from($max) < <$upper_type>::max_value());
			}

			#[derive(Encode, Decode, PartialEq, Eq, RuntimeDebug)]
			struct WithCompact<T: codec::HasCompact> {
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
					let compact: codec::Compact<$name> = $name(n).into();
					let encoded = compact.encode();
					assert_eq!(encoded.len(), l);
					let decoded = <codec::Compact<$name>>::decode(&mut & encoded[..])
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
				assert_eq!($name::ACCURACY, $max);
				assert_eq!($name::from_percent(0), $name::from_parts(Zero::zero()));
				assert_eq!($name::from_percent(10), $name::from_parts($max / 10));
				assert_eq!($name::from_percent(100), $name::from_parts($max));
				assert_eq!($name::from_percent(200), $name::from_parts($max));
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
				let max_value = <$upper_type>::from($max);
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
					$name::from_parts((4 * <$upper_type>::from($max) / 100 / 100) as $type)
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

			#[test]
			fn saturating_pow_works() {
				// x^0 == 1
				assert_eq!(
					$name::from_parts($max / 2).saturating_pow(0), 
					$name::from_parts($max),
				);

				// x^1 == x
				assert_eq!(
					$name::from_parts($max / 2).saturating_pow(1), 
					$name::from_parts($max / 2),
				);

				// x^2
				assert_eq!(
					$name::from_parts($max / 2).saturating_pow(2), 
					$name::from_parts($max / 2).square(),
				);

				// x^3
				assert_eq!(
					$name::from_parts($max / 2).saturating_pow(3), 
					$name::from_parts($max / 8),
				);

				// 0^n == 0
				assert_eq!(
					$name::from_parts(0).saturating_pow(3), 
					$name::from_parts(0),
				);

				// 1^n == 1
				assert_eq!(
					$name::from_parts($max).saturating_pow(3), 
					$name::from_parts($max),
				);

				// (x < 1)^inf == 0 (where 2.pow(31) ~ inf)
				assert_eq!(
					$name::from_parts($max / 2).saturating_pow(2usize.pow(31)), 
					$name::from_parts(0),
				);
			}

			#[test]
			fn saturating_reciprocal_mul_works() {
				// divide by 1
				assert_eq!(
					$name::from_parts($max).saturating_reciprocal_mul(<$type>::from(10u8), false),
					10,
				);
				// divide by 1/2
				assert_eq!(
					$name::from_parts($max / 2).saturating_reciprocal_mul(<$type>::from(10u8), false),
					20,
				);
				// saturate
				assert_eq!(
					$name::from_parts(1).saturating_reciprocal_mul($max, false),
					<$type>::max_value(),
				);
				// round to nearest 
				assert_eq!(
					$name::from_percent(60).saturating_reciprocal_mul(<$type>::from(10u8), false),
					17,
				);
				// round down
				assert_eq!(
					$name::from_percent(60).saturating_reciprocal_mul(<$type>::from(10u8), true),
					16,
				);
			}

			#[test]
			fn saturating_truncating_mul_works() {
				assert_eq!(
					$name::from_percent(49).overflow_prune_mul(10 as $type, true), 
					4,
				);
				assert_eq!(
					$name::from_percent(50).overflow_prune_mul(($max as $upper_type).pow(2), true), 
					($max as $upper_type).pow(2) / 2,
				);
			}

            #[test]
            fn rational_mul_correction_works() {
                assert_eq!(
                    super::rational_mul_correction::<$type, $name>(
                        <$type>::max_value(), 
                        <$type>::max_value(), 
                        <$type>::max_value(), 
                        false,
                    ),
                    0,
                );
                assert_eq!(
                    super::rational_mul_correction::<$type, $name>(
                        <$type>::max_value() - 1, 
                        <$type>::max_value(), 
                        <$type>::max_value(), 
                        false,
                    ),
                    <$type>::max_value() - 1,
                );
                assert_eq!(
                    super::rational_mul_correction::<$upper_type, $name>(
                        ((<$type>::max_value() - 1) as $upper_type).pow(2), 
                        <$type>::max_value(), 
                        <$type>::max_value(), 
                        false,
                    ),
                    1,
                );
                // ((max^2 - 1) % max) * max / max == max - 1
                assert_eq!(
                    super::rational_mul_correction::<$upper_type, $name>(
                        (<$type>::max_value() as $upper_type).pow(2) - 1, 
                        <$type>::max_value(), 
                        <$type>::max_value(), 
                        false,
                    ),
                    (<$type>::max_value() - 1).into(),
                );
                // (max % 2) * max / 2 == max / 2
                assert_eq!(
                    super::rational_mul_correction::<$upper_type, $name>(
                        (<$type>::max_value() as $upper_type).pow(2), 
                        <$type>::max_value(), 
                        2 as $type,
                        false,
                    ),
                    <$type>::max_value() as $upper_type / 2,
                );
                // ((max^2 - 1) % max) * 2 / max == 2 (rounded up)
                assert_eq!(
                    super::rational_mul_correction::<$upper_type, $name>(
                        (<$type>::max_value() as $upper_type).pow(2) - 1, 
                        2 as $type,
                        <$type>::max_value(), 
                        false,
                    ),
                    2,
                );
                // ((max^2 - 1) % max) * 2 / max == 1 (truncated)
                assert_eq!(
                    super::rational_mul_correction::<$upper_type, $name>(
                        (<$type>::max_value() as $upper_type).pow(2) - 1, 
                        2 as $type,
                        <$type>::max_value(), 
                        true,
                    ),
                    1,
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
