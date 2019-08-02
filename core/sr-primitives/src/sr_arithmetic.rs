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

//! Minimal, mostly not efficient, fixed point arithmetic primitives for runtime.

#[cfg(feature = "std")]
use crate::serde::{Serialize, Deserialize};
use rstd::{prelude::*, ops, convert::{TryInto, TryFrom}};
use codec::{Encode, Decode};
use crate::traits::{SimpleArithmetic, SaturatedConversion, CheckedSub, CheckedAdd, Bounded, UniqueSaturatedInto, Saturating};

macro_rules! implement_per_thing {
	($name:ident, $test_mod:ident, $max:tt, $type:ty, $upper_type:ty, $title:expr) => {
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

			/// From an explicitly defined number of parts per maximum of the type.
			///
			/// This can be called at compile time.
			pub const fn from_parts(parts: $type) -> Self {
				Self([parts, $max][(parts > $max) as usize])
			}

			/// Converts from a percent. Equal to `x / 100`.
			///
			/// This can be created at compile time.
			pub const fn from_percent(x: $type) -> Self { Self([x, 100][(x > 100) as usize] * ($max / 100)) }

			/// Converts a fraction into `Permill`.
			#[cfg(feature = "std")]
			pub fn from_fraction(x: f64) -> Self { Self((x * ($max as f64)) as $type) }

			/// Approximate the fraction `p/q` into a per million fraction.
			///
			/// The computation of this approximation is performed in the generic type `N`.
			///
			/// Should never overflow.
			pub fn from_rational_approximation<N>(p: N, q: N) -> Self
				where N: SimpleArithmetic + Clone
			{
				// q cannot be zero.
				let q = q.max(1u32.into());
				// p should not be bigger than q.
				let p = p.min(q.clone());

				let factor = (q.clone() / $max.into()).max((1 as $type).into());

				// q cannot overflow: (q / (q/$max)) < $max. p < q hence p also cannot overflow.
				let p_reduce: $type = (p / factor.clone()).try_into().unwrap_or_else(|_| panic!());
				let q_reduce: $type = (q / factor.clone()).try_into().unwrap_or_else(|_| panic!());
				// `p_reduced` and `q_reduced` are withing $type. Mul by another $max will always
				// fit in $upper_type. This is guaranteed by the macro tests.
				let part = p_reduce as $upper_type * ($max as $upper_type) / q_reduce as $upper_type;

				$name(part as $type)
			}
		}

		/// Overflow-prune multiplication.
		///
		/// tailored to be used with a balance type. Never overflows.
		impl<N> ops::Mul<N> for $name
		where
			N: Clone + From<u32> + UniqueSaturatedInto<u32> + ops::Rem<N, Output=N>
				+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
		{
			type Output = N;
			fn mul(self, b: N) -> Self::Output {
				let maximum: N = $max.into();
				let part: N = self.0.into();

				let rem_multiplied_divided = {
					let rem = b.clone().rem(maximum.clone());

					// `rem_sized` is inferior to $max, thus it fits into $type. This is assured by
					// a test.
					let rem_sized = rem.saturated_into::<$type>();

					// `self` and `rem_sized` are inferior to $max, thus the product is less than
					// $max^2 and fits into $upper_type. This is assured by a test.
					let rem_multiplied_upper = rem_sized as $upper_type * self.0 as $upper_type;

					// `rem_multiplied_upper` is less than $max^2 therefore divided by $max it fits into
					// u32
					let rem_multiplied_divided_sized = (rem_multiplied_upper / ($max as $upper_type)) as u32;

					// `rem_multiplied_divided_sized` is inferior to b, thus it can be converted back to N type
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
			use super::$name;

			#[derive(Encode, Decode, PartialEq, Eq, Debug)]
			struct WithCompact<T: crate::codec::HasCompact> {
				data: T,
			}

			#[test]
			fn macro_expanded_correctly() {
				assert!($max < <$type>::max_value());
				assert!(($max as $upper_type) < <$upper_type>::max_value());
				// for something like percent they can be the same.
				assert!((<$type>::max_value() as $upper_type) <= <$upper_type>::max_value());
				assert!(($max as $upper_type).checked_mul($max.into()).is_some());
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
					(0 as $type, 1usize),
					(63, 1), (64, 2),
					(16383, 2),
					(16384, 4),
					(1073741823, 4),
					(1073741824, 5),
					(<$type>::max_value(), 5)
				];
				for &(n, l) in &tests {
					let compact: crate::codec::Compact<$name> = $name(n).into();
					let encoded = compact.encode();
					assert_eq!(encoded.len(), l);
					let decoded = <crate::codec::Compact<$name>>::decode(&mut & encoded[..]).unwrap();
					let per_thingy: $name = decoded.into();
					assert_eq!(per_thingy, $name(n));
				}
			}

			macro_rules! per_thing_mul_test {
				($num_type:tt) => {
					// multiplication from all sort of from_percent
					assert_eq!($name::from_percent(100) * $num_type::max_value(), $num_type::max_value());
					assert_eq!(
						$name::from_percent(99) * $num_type::max_value(),
						((Into::<U256>::into($num_type::max_value()) * 99u32) / 100u32).as_u128() as $num_type
					);
					assert_eq!($name::from_percent(50) * $num_type::max_value(), $num_type::max_value() / 2);
					assert_eq!($name::from_percent(1) * $num_type::max_value(), $num_type::max_value() / 100);
					assert_eq!($name::from_percent(0) * $num_type::max_value(), 0);

					// multiplication with bounds
					assert_eq!($name::one() * $num_type::max_value(), $num_type::max_value());
					assert_eq!($name::zero() * $num_type::max_value(), 0);
				}
			}

			#[test]
			fn per_thing_mul_works() {
				use primitive_types::U256;
				per_thing_mul_test!(u32);
				per_thing_mul_test!(u64);
				per_thing_mul_test!(u128);
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
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 3),
						$name::from_fraction(0.33333333333333333333333333333),
					);
					assert_eq!(
						$name::from_rational_approximation(1 as $num_type, 10),
						$name::from_percent(10),
					);

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
						$name::from_rational_approximation(1, $max+1),
						$name::zero(),
					);

					// no accurate anymore but won't overflow.
					assert_eq!(
						$name::from_rational_approximation($num_type::max_value() - 1, $num_type::max_value()),
						$name::one(),
					);
					assert_eq!(
						$name::from_rational_approximation($num_type::max_value() / 3, $num_type::max_value()),
						$name::from_parts($name::one().0 / 3),
					);
					assert_eq!(
						$name::from_rational_approximation(1, $num_type::max_value()),
						$name::zero(),
					);
				};
			}

			#[test]
			fn per_thing_from_rationale_approx_works() {
				per_thing_from_rationale_approx_test!(u32);
				per_thing_from_rationale_approx_test!(u64);
				per_thing_from_rationale_approx_test!(u128);
			}

			#[test]
			fn per_thing_multiplication_with_large_number() {
				use primitive_types::U256;
				let max_minus_one = $max - 1;
				assert_eq!(
					$name::from_parts(max_minus_one) * std::u128::MAX,
					((Into::<U256>::into(std::u128::MAX) * max_minus_one) / $max).as_u128()
				);
			}

			#[test]
			fn per_things_mul_operates_in_output_type() {
				assert_eq!($name::from_percent(50) * 100u32, 50u32);
				assert_eq!($name::from_percent(50) * 100u64, 50u64);
				assert_eq!($name::from_percent(50) * 100u128, 50u128);
			}
		}
	};
}

implement_per_thing!(Permill, test_permill, 1_000_000u32, u32, u64, "_Parts per Million_");
implement_per_thing!(Perbill, test_perbill, 1_000_000_000u32, u32, u64, "_Parts per Billion_");
implement_per_thing!(Percent, test_per_cent, 100u32, u32, u32, "_Percent_");

/// An unsigned fixed point number. Can hold any value in the range [-9_223_372_036, 9_223_372_036]
/// with fixed point accuracy of one billion.
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed64(i64);

/// The maximum value of the `Fixed64` type
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
	/// Returns a saturated `n + (self * n)`.
	pub fn saturated_multiply_accumulate<N>(&self, int: N) -> N
	where
		N: TryFrom<u64> + From<u32> + UniqueSaturatedInto<u32> + Bounded + Clone + Saturating +
		ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
		ops::Add<N, Output=N>,
	{
		let parts = self.0;
		let positive = parts > 0;

		// will always fit.
		let natural_parts: u64 = (parts / DIV) as u64;
		// might saturate.
		let natural_parts: N = natural_parts.saturated_into();
		// fractional parts can always fit into u32.
		let perbill_parts = (parts.abs() % DIV) as u32;

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

/// PerU128 is parts-per-u128-max-value. It stores a value between 0 and 1 in fixed point.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct PerU128(u128);

const U128: u128 = u128::max_value();

impl PerU128 {
	/// Nothing.
	pub fn zero() -> Self { Self(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Self { Self(U128) }

	/// From an explicitly defined number of parts per maximum of the type.
	pub fn from_parts(x: u128) -> Self { Self(x) }

	/// Construct new instance where `x` is denominator and the nominator is 1.
	pub fn from_xth(x: u128) -> Self { Self(U128/x.max(1)) }
}

impl ::rstd::ops::Deref for PerU128 {
	type Target = u128;

	fn deref(&self) -> &u128 {
		&self.0
	}
}

impl codec::CompactAs for PerU128 {
	type As = u128;
	fn encode_as(&self) -> &u128 {
		&self.0
	}
	fn decode_from(x: u128) -> PerU128 {
		Self(x)
	}
}

impl From<codec::Compact<PerU128>> for PerU128 {
	fn from(x: codec::Compact<PerU128>) -> PerU128 {
		x.0
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

	macro_rules! saturating_mul_acc_test {
		($num_type:tt) => {
			assert_eq!(Fixed64::from_rational(100, 1).saturated_multiply_accumulate(10 as $num_type), 1010);
			assert_eq!(Fixed64::from_rational(100, 2).saturated_multiply_accumulate(10 as $num_type), 510);
			assert_eq!(Fixed64::from_rational(100, 3).saturated_multiply_accumulate(0 as $num_type), 0);
			assert_eq!(Fixed64::from_rational(5, 1).saturated_multiply_accumulate($num_type::max_value()), $num_type::max_value());
			assert_eq!(max().saturated_multiply_accumulate($num_type::max_value()), $num_type::max_value());
		}
	}

	#[test]
	fn fixed64_multiply_accumulate_works() {
		saturating_mul_acc_test!(u32);
		saturating_mul_acc_test!(u64);
		saturating_mul_acc_test!(u128);
	}
}
