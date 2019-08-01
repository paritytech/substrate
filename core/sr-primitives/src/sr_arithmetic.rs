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

use rstd::{prelude::*, ops};
use codec::{Encode, Decode};
use crate::serde::{Serialize, Deserialize};
use crate::traits::{self, SaturatedConversion};

macro_rules! implement_per_thing {
	($name:ident, $test_mod:ident, $max:expr, $type:ty, $upper_type:ty, $title:expr) => {
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
			/// The computation of this approximation is performed in the generic type `N`. to
			/// ensure overflow wont' happen, TODO TODO.
			pub fn from_rational_approximation<N>(p: N, q: N) -> Self
				where N: traits::SimpleArithmetic + Clone
			{
				// q cannot be zero.
				let q = q.max(1u32.into());
				// p should not be bigger than q.
				let p = p.min(q.clone());
				let factor = (q.clone() / $max.into()).max((1 as $type).into());

				// Conversion can't overflow as p < q so ( p / (q/million)) < million
				let p_reduce: $type = (p / factor.clone()).try_into().unwrap_or_else(|_| panic!());
				let q_reduce: $type = (q / factor.clone()).try_into().unwrap_or_else(|_| panic!());
				// `p_reduced` and `q_reduced` are withing $type. Mul by another $max will always
				// fit in $upper_type. TODO test for this.
				let part = p_reduce as $upper_type * ($max as $upper_type) / q_reduce as $upper_type;

				$name(part as $type)
			}
		}

		/// Overflow-prune multiplication.
		///
		/// tailored to be used with a balance type.
		impl<N> ops::Mul<N> for $name
		where
			N: Clone + From<u32> + traits::UniqueSaturatedInto<u32> + ops::Rem<N, Output=N>
				+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
		{
			type Output = N;
			fn mul(self, b: N) -> Self::Output {
				let maximum: N = $max.into();
				let part: N = self.0.into();

				let rem_multiplied_divided = {
					let rem = b.clone().rem(maximum.clone());

					// `rem` is inferior to $max, thus it fits into $type (assured by a test)
					let rem_sized = rem.saturated_into::<$type>();

					// `self` and `rem` are inferior to $max, thus the product is less than 10^12
					// and fits into u64
					let rem_multiplied_upper = rem_sized as $upper_type * self.0 as $upper_type;

					// `rem_multiplied_upper` is less than 10^12 therefore divided by $max it fits into
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
				assert!((<$type>::max_value() as $upper_type) < <$upper_type>::max_value());
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

				};
			}
			#[test]
			fn per_thing_from_rationale_approx_works() {
				assert_eq!(
					$name::from_rational_approximation(1u128, 1),
					$name::one(),
				);
				assert_eq!(
					$name::from_rational_approximation(1u128, 3),
					$name::from_fraction(0.33333333333333),
				);
				assert_eq!(
					$name::from_rational_approximation(1u128, 10),
					$name::from_percent(10),
				);
				assert_eq!(
					$name::from_rational_approximation(u128::max_value() - 1, u128::max_value()),
					$name::one(),
				);
				assert_eq!(
					$name::from_rational_approximation(u128::max_value() / 3, u128::max_value()),
					$name::from_parts($name::one().0 / 3),
				);
				assert_eq!(
					$name::from_rational_approximation(1, u128::max_value()),
					$name::zero(),
				);


			}
		}


	};
}

implement_per_thing!(Permill, test_permill, 1_000_000u32, u32, u64, "_Parts per Million_");
implement_per_thing!(PerFoo, test_perfoo, 1_000_000_000u32, u32, u64, "_Parts per Foo_");

/// Perbill is parts-per-billion. It stores a value between 0 and 1 in fixed point and
/// provides a means to multiply some other value by that.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Perbill(u32);

impl Perbill {
	/// Nothing.
	pub fn zero() -> Self { Self(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Self { Self(1_000_000_000) }

	/// create a new raw instance. This can be called at compile time.
	pub const fn from_const_parts(parts: u32) -> Self {
		Self([parts, 1_000_000_000][(parts > 1_000_000_000) as usize])
	}

	/// From an explicitly defined number of parts per maximum of the type.
	pub fn from_parts(parts: u32) -> Self { Self::from_const_parts(parts) }

	/// Converts from a percent. Equal to `x / 100`.
	pub const fn from_percent(x: u32) -> Self { Self([x, 100][(x > 100) as usize] * 10_000_000) }

	/// Construct new instance where `x` is in millionths. Value equivalent to `x / 1,000,000`.
	pub fn from_millionths(x: u32) -> Self { Self(x.min(1_000_000) * 1000) }

	#[cfg(feature = "std")]
	/// Construct new instance whose value is equal to `x` (between 0 and 1).
	pub fn from_fraction(x: f64) -> Self { Self((x.max(0.0).min(1.0) * 1_000_000_000.0) as u32) }

	/// Approximate the fraction `p/q` into a per billion fraction
	pub fn from_rational_approximation<N>(p: N, q: N) -> Self
		where N: traits::SimpleArithmetic + Clone
	{
		let p = p.min(q.clone());
		let factor = (q.clone() / 1_000_000_000u32.into()).max(1u32.into());

		// Conversion can't overflow as p < q so ( p / (q/billion)) < billion
		let p_reduce: u32 = (p / factor.clone()).try_into().unwrap_or_else(|_| panic!());
		let q_reduce: u32 = (q / factor.clone()).try_into().unwrap_or_else(|_| panic!());
		let part = p_reduce as u64 * 1_000_000_000u64 / q_reduce as u64;

		Perbill(part as u32)
	}
}

impl<N> ops::Mul<N> for Perbill
where
	N: Clone + From<u32> + traits::UniqueSaturatedInto<u32> + ops::Rem<N, Output=N>
	+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
{
	type Output = N;
	fn mul(self, b: N) -> Self::Output {
		let billion: N = 1_000_000_000.into();
		let part: N = self.0.into();

		let rem_multiplied_divided = {
			let rem = b.clone().rem(billion.clone());

			// `rem` is inferior to one billion, thus it fits into u32
			let rem_u32 = rem.saturated_into::<u32>();

			// `self` and `rem` are inferior to one billion, thus the product is less than 10^18
			// and fits into u64
			let rem_multiplied_u64 = rem_u32 as u64 * self.0 as u64;

			// `rem_multiplied_u64` is less than 10^18 therefore divided by a billion it fits into
			// u32
			let rem_multiplied_divided_u32 = (rem_multiplied_u64 / 1_000_000_000) as u32;

			// `rem_multiplied_divided` is inferior to b, thus it can be converted back to N type
			rem_multiplied_divided_u32.into()
		};

		(b / billion) * part + rem_multiplied_divided
	}
}

#[cfg(feature = "std")]
impl From<f64> for Perbill {
	fn from(x: f64) -> Perbill {
		Perbill::from_fraction(x)
	}
}

#[cfg(feature = "std")]
impl From<f32> for Perbill {
	fn from(x: f32) -> Perbill {
		Perbill::from_fraction(x as f64)
	}
}

impl codec::CompactAs for Perbill {
	type As = u32;
	fn encode_as(&self) -> &u32 {
		&self.0
	}
	fn decode_from(x: u32) -> Perbill {
		Perbill(x)
	}
}

impl From<codec::Compact<Perbill>> for Perbill {
	fn from(x: codec::Compact<Perbill>) -> Perbill {
		x.0
	}
}

#[cfg(test)]
mod per_thing_tests {
	use super::{Perbill, Permill};

	#[test]
	fn per_things_operate_in_output_type() {
		assert_eq!(Perbill::one() * 255_u64, 255);
	}

	#[test]
	fn per_things_one_minus_one_part() {
		use primitive_types::U256;

		assert_eq!(
			Perbill::from_parts(999_999_999) * std::u128::MAX,
			((Into::<U256>::into(std::u128::MAX) * 999_999_999u32) / 1_000_000_000u32).as_u128()
		);

		assert_eq!(
			Permill::from_parts(999_999) * std::u128::MAX,
			((Into::<U256>::into(std::u128::MAX) * 999_999u32) / 1_000_000u32).as_u128()
		);
	}
}

