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
use crate::traits::{SaturatedConversion, UniqueSaturatedInto, Saturating};
use sp_debug_derive::RuntimeDebug;

macro_rules! implement_per_thing {
	($name:ident, $test_mod:ident, [$($test_units:tt),+], $max:tt, $type:ty, $upper_type:ty, $title:expr $(,)?) => {
		/// A fixed point representation of a number between in the range [0, 1].
		///
		#[doc = $title]
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
		#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, RuntimeDebug, CompactAs)]
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

			/// Converts a percent into `Self`. Equal to `x / 100`.
			///
			/// This can be created at compile time.
			pub const fn from_percent(x: $type) -> Self {
				Self([x, 100][(x > 100) as usize] * ($max / 100))
			}

			/// Return the product of multiplication of this value by itself.
			pub fn square(self) -> Self {
				// both can be safely casted and multiplied.
				let p: $upper_type = self.0 as $upper_type * self.0 as $upper_type;
				let q: $upper_type = <$upper_type>::from($max) * <$upper_type>::from($max);
				Self::from_rational_approximation(p, q)
			}

			/// Converts a fraction into `Self`.
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
					* <$upper_type>::from($max)
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
				let m = <$upper_type>::from($max);
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

		#[cfg(test)]
		mod $test_mod {
			use codec::{Encode, Decode};
			use super::{$name, Saturating, RuntimeDebug};
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
