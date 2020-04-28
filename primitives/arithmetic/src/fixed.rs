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

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};

use sp_std::{ops, fmt, prelude::*, convert::TryInto};
use codec::{Encode, CompactAs};
use crate::traits::{
	SaturatedConversion, UniqueSaturatedInto, Saturating, BaseArithmetic,
	Bounded, Zero, FixedPointNumber
};
use crate::helpers_128bit::divide;
use sp_debug_derive::RuntimeDebug;

#[macro_export]
macro_rules! implement_fixed {
	(
		$name:ident,
		$inner_type:ty,
		$unsigned_type:ty,
		$prev_unsigned_type:ty,
		$perthing_type:ty,
		$div:tt,
		$precision:tt,
	) => {
		#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
		pub struct $name($inner_type);

		impl From<$inner_type> for $name {
			fn from(int: $inner_type) -> Self {
				$name::from_integer(int)
			}
		}

		impl From<($inner_type, $inner_type)> for $name {
			fn from(r: ($inner_type, $inner_type)) -> Self {
				$name::from_rational(r.0, r.1)
			}
		}

		impl FixedPointNumber for $name {
			type Inner = $inner_type;
			type Unsigned = $unsigned_type;
			type PrevUnsigned = $prev_unsigned_type;
			type Perthing = $perthing_type;

			const BITS: u8 = $div;

			fn from_inner(inner: Self::Inner) -> Self {
				Self(inner)
			}

			fn into_inner(self) -> Self::Inner {
				self.0
			}

			fn from_integer(int: Self::Inner) -> Self {
				Self(int.saturating_mul(Self::accuracy()))
			}

			fn checked_from_integer(int: Self::Inner) -> Option<Self> {
				int.checked_mul(Self::accuracy()).map(|inner| Self(inner))
			}

			fn from_rational<N: UniqueSaturatedInto<Self::Inner>>(n: N, d: Self::Inner) -> Self {
				let n = n.unique_saturated_into();

				let signum = n.signum() * d.signum();

				let n = n.checked_abs().map(|v| v as u128)
					.unwrap_or(Self::Inner::max_value() as u128 + 1);
				let d = d.checked_abs().map(|v| v as u128)
					.unwrap_or(Self::Inner::max_value() as u128 + 1);
				
				divide(n, d, Self::BITS)
					.and_then(|r| r.try_into().ok())
					.map(|n: Self::Inner| Self(n.saturating_mul(signum)))
					.unwrap_or_else(||
						if signum >= 0 {
							Self::max_value()
						} else {
							Self::min_value()
						}
					)
			}

			fn checked_mul_int<N>(self, int: N) -> Option<N>
			where
				N: TryFrom<i128> + UniqueSaturatedInto<i128> +
				Copy + Bounded + Saturating +
				ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
				ops::Add<N, Output=N>,
			{
				let rhs: i128 = int.unique_saturated_into();
				let lhs: i128 = self.0.unique_saturated_into();
				let signum = rhs.signum() * lhs.signum();

				let lhs = lhs.checked_abs().map(|v| v as u128)
					.unwrap_or(Self::Inner::max_value() as u128 + 1);
				let rhs = rhs.checked_abs().map(|v| v as u128)
					.unwrap_or(N::max_value().unique_saturated_into() as u128 + 1);

				let (carry, result) = multiply(lhs, rhs);

				// Get the shift to move upper bits to original place and at the same time
				// to perform the division that give us the integer part of the fraction.
				let carry_shift = 128.checked_sub(&Self::BITS).expect("128 > BITS; qed").into();

				if carry.leading_zeros() < carry_shift {
					// Overflow.
					return None
				}

				let low = result.checked_shr(Self::BITS.into()).expect("128 > BITS; qed");

				carry.checked_shl(carry_shift)
					.and_then(|c| low.checked_add(c))
					.and_then(|r| r.try_into().ok())
					.map(|r: i128| r * signum)
					.and_then(|r| r.try_into().ok())
			}

			fn checked_div_int<N>(self, other: N) -> Option<N>
			where
				N: Copy + TryFrom<i128> + UniqueSaturatedInto<i128>,
			{
				let lhs: i128 = self.0.unique_saturated_into();
				let rhs: i128 = other.unique_saturated_into();

				lhs.checked_div(rhs)
					.and_then(|inner| inner.checked_div(Self::accuracy().into()))
					.and_then(|n| TryInto::<N>::try_into(n).ok())
			}

			fn saturating_mul_int<N>(self, other: N) -> N
			where
				N: TryFrom<i128> + UniqueSaturatedInto<i128> +
				Copy + Bounded + Saturating +
				ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
				ops::Add<N, Output=N>,
			{
				self.checked_mul_int(other).unwrap_or_else(|| {
					let signum = other.unique_saturated_into().signum() * self.0.signum() as i128;
					if signum.is_negative() {
						Bounded::min_value()
					} else {
						Bounded::max_value()
					}
				})
			}

			fn saturating_abs(self) -> Self {
				Self(self.0.checked_abs().unwrap_or(Self::Inner::max_value()))
			}

			fn zero() -> Self {
				Self(0)
			}

			fn is_zero(&self) -> bool {
				self.0 == 0
			}

			fn one() -> Self {
				Self(Self::accuracy())
			}

			fn is_positive(self) -> bool {
				self.0.is_positive()
			}

			fn is_negative(self) -> bool {
				self.0.is_negative()
			}

			fn saturated_multiply_accumulate<N>(self, int: N) -> N
				where
					N: TryFrom<i128> + UniqueSaturatedInto<i128> +
					Copy + Bounded + Saturating +
					ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
					ops::Add<N, Output=N>,
			{
				self.saturating_mul_int(int).saturating_add(int)
			}
		}

		impl Saturating for $name {
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

		impl ops::Neg for $name {
			type Output = Self;

			fn neg(self) -> Self::Output {
				Self(self.0.saturating_mul(-1))
			}
		}

		impl ops::Add for $name {
			type Output = Self;

			fn add(self, rhs: Self) -> Self::Output {
				Self(self.0 + rhs.0)
			}
		}

		impl ops::Sub for $name {
			type Output = Self;

			fn sub(self, rhs: Self) -> Self::Output {
				Self(self.0 - rhs.0)
			}
		}

		impl ops::Mul for $name {
			type Output = Self;

			fn mul(self, rhs: Self) -> Self::Output {
				Self((self.0 * rhs.0) / Self::accuracy())
			}
		}

		impl ops::Div for $name {
			type Output = Self;

			fn div(self, rhs: Self) -> Self::Output {
				Self((self.0 * Self::accuracy()) / rhs.0)
			}
		}

		impl CheckedSub for $name {
			fn checked_sub(&self, rhs: &Self) -> Option<Self> {
				self.0.checked_sub(rhs.0).map(Self)
			}
		}

		impl CheckedAdd for $name {
			fn checked_add(&self, rhs: &Self) -> Option<Self> {
				self.0.checked_add(rhs.0).map(Self)
			}
		}

		impl CheckedDiv for $name {
			fn checked_div(&self, other: &Self) -> Option<Self> {
				let n = self.0;
				let d = other.0;

				let signum = n.signum() * d.signum();
				let max_value = <Self as FixedPointNumber>::Inner::max_value() as u128;
				let n = n.checked_abs().map(|v| v as u128).unwrap_or(max_value + 1);
				let d = d.checked_abs().map(|v| v as u128).unwrap_or(max_value + 1);
				
				divide(n, d, <Self as FixedPointNumber>::BITS)
					.and_then(|r|
						if r == max_value + 1 && signum < 0 {
							let r = r.checked_sub(1)?;
							let r: <Self as FixedPointNumber>::Inner = r.try_into().ok()?;
							let r = r.checked_mul(signum)?;
							r.checked_sub(1)
						} else {
							let r: <Self as FixedPointNumber>::Inner = r.try_into().ok()?;
							r.checked_mul(signum)
						}
					)
					.map(|r| Self(r))
			}
		}

		impl CheckedMul for $name {
			fn checked_mul(&self, rhs: &Self) -> Option<Self> {
				let signum = self.0.signum() * rhs.0.signum();
				let max_value = <Self as FixedPointNumber>::Inner::max_value() as u128;
				let n: u128 = self.0.checked_abs().map(|v| v as u128).unwrap_or(max_value + 1);
				let d: u128 = rhs.0.checked_abs().map(|v| v as u128).unwrap_or(max_value + 1);

				let (carry, result) = multiply(n, d);

				let carry_shift = 128.checked_sub(&Self::BITS).expect("128 > BITS; qed").into();

				if carry.leading_zeros() < carry_shift {
					// Overflow.
					return None
				}

				let low: u128 = result.checked_shr(Self::BITS.into()).expect("128 > BITS; qed");

				carry.checked_shl(carry_shift)
					.and_then(|c| low.checked_add(c))
					.and_then(|r| r.try_into().ok())
					.and_then(|r: <Self as FixedPointNumber>::Inner| r.checked_mul(signum))
					.map(|r| Self(r))
			}
		}

		impl Bounded for $name {
			fn min_value() -> Self {
				Self(<Self as FixedPointNumber>::Inner::min_value())
			}

			fn max_value() -> Self {
				Self(<Self as FixedPointNumber>::Inner::max_value())
			}
		}

		impl sp_std::fmt::Debug for $name {
			#[cfg(feature = "std")]
			fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
				let integral = {
					let int = self.0 / Self::accuracy();
					let signum_for_zero = if int == 0 && self.is_negative() { "-" } else { "" };
					format!("{}{}", signum_for_zero, int)
				};
				let fractional = format!("{:0>width$}", (self.0 % Self::accuracy()).abs(), width=$precision);
				write!(f, "{}({}.{})", stringify!($name), integral, fractional)
			}

			#[cfg(not(feature = "std"))]
			fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
				Ok(())
			}
		}

		impl<P: PerThing> From<P> for $name {
			fn from(p: P) -> Self {
				let accuracy = P::ACCURACY.saturated_into() as <Self as FixedPointNumber>::Inner;
				let value = p.deconstruct().saturated_into() as <Self as FixedPointNumber>::Inner;
				$name::from_rational(value, accuracy)
			}
		}

		#[cfg(feature = "std")]
		impl sp_std::fmt::Display for $name {
			fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
				write!(f, "{}", self.0)
			}
		}

		#[cfg(feature = "std")]
		impl sp_std::str::FromStr for $name {
			type Err = &'static str;

			fn from_str(s: &str) -> Result<Self, Self::Err> {
				let inner: <Self as FixedPointNumber>::Inner = s.parse()
					.map_err(|_| "invalid string input for fixed point number")?;
				Ok(Self::from_inner(inner))
			}
		} 

		// Manual impl `Serialize` as serde_json does not support i128.
		// TODO: remove impl if issue https://github.com/serde-rs/json/issues/548 fixed.
		#[cfg(feature = "std")]
		impl Serialize for $name {
			fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
			where
				S: Serializer,
			{
				serializer.serialize_str(&self.to_string())
			}
		}

		// Manual impl `Serialize` as serde_json does not support i128.
		// TODO: remove impl if issue https://github.com/serde-rs/json/issues/548 fixed.
		#[cfg(feature = "std")]
		impl<'de> Deserialize<'de> for $name {
			fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
			where
				D: Deserializer<'de>,
			{
				use sp_std::str::FromStr;
				let s = String::deserialize(deserializer)?;
				$name::from_str(&s).map_err(|err_str| de::Error::custom(err_str))
			}
		}

		#[cfg(test)]
		mod tests {
			use super::*;
			use crate::{Perbill, Percent, Permill, Perquintill};

			fn max() -> $name {
				$name::max_value()
			}

			fn min() -> $name {
				$name::min_value()
			}

			#[test]
			fn from_integer_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				// Cases where integer fits.
				let a = $name::from_integer(42);
				assert_eq!(a.into_inner(), 42 * accuracy);

				let a = $name::from_integer(-42);
				assert_eq!(a.into_inner(), -42 * accuracy);

				// Max/min integers that fit.
				let a = $name::from_integer(inner_max / accuracy);
				assert_eq!(a.into_inner(), (inner_max / accuracy) * accuracy);

				let a = $name::from_integer(inner_min / accuracy);
				assert_eq!(a.into_inner(), (inner_min / accuracy) * accuracy);

				// Cases where integer doesn't fit, so it saturates.
				let a = $name::from_integer(inner_max / accuracy + 1);
				assert_eq!(a.into_inner(), inner_max);

				let a = $name::from_integer(inner_min / accuracy - 1);
				assert_eq!(a.into_inner(), inner_min);
			}

			#[test]
			fn checked_from_integer_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				// Cases where integer fits.
				let a = $name::checked_from_integer(42)
					.expect("42 * accuracy <= inner_max; qed");
				assert_eq!(a.into_inner(), 42 * accuracy);

				let a = $name::checked_from_integer(-42)
					.expect("-42 * accuracy >= inner_min; qed");
				assert_eq!(a.into_inner(), -42 * accuracy);

				// Max/min integers that fit.
				let a = $name::checked_from_integer(inner_max / accuracy)
					.expect("(inner_max / accuracy) * accuracy <= inner_max; qed");
				assert_eq!(a.into_inner(), (inner_max / accuracy) * accuracy);

				let a = $name::checked_from_integer(inner_min / accuracy)
					.expect("(inner_min / accuracy) * accuracy <= inner_min; qed");
				assert_eq!(a.into_inner(), (inner_min / accuracy) * accuracy);

				// Cases where integer doesn't fit, so it returns `None`.
				let a = $name::checked_from_integer(inner_max / accuracy + 1);
				assert_eq!(a, None);

				let a = $name::checked_from_integer(inner_min / accuracy - 1);
				assert_eq!(a, None);
			}

			#[test]
			fn from_inner_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();

				assert_eq!(max(), $name::from_inner(inner_max));
				assert_eq!(min(), $name::from_inner(inner_min));
			}

			#[test]
			fn from_rational_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				let a = $name::from_rational(5, 2);
				let b = $name::from_rational(-5, 2);
				let c = $name::from_rational(5, -2);
				let d = $name::from_rational(-5, -2);

				let e = $name::from_rational(inner_max, accuracy);
				let f = $name::from_rational(inner_min, accuracy);
				let g = $name::from_rational(inner_max, -accuracy);
				let h = $name::from_rational(inner_min, -accuracy);
				let i = $name::from_rational(inner_min + 1, -accuracy);

				let j = $name::from_rational(42, 0);

				let k = $name::from_rational(inner_max, 1);
				let l = $name::from_rational(inner_min, 1);
				let m = $name::from_rational(inner_min, -1);
				let n = $name::from_rational(inner_max, -1);

				let o = $name::from_rational(inner_max, inner_max);
				let p = $name::from_rational(inner_min, inner_min);
				let r = $name::from_rational(inner_max, -inner_max);
				let s = $name::from_rational(-inner_max, inner_max);

				let t = $name::from_rational(inner_max, 3 * accuracy);
				let u = $name::from_rational(inner_max, -3 * accuracy);

				let v = $name::from_rational(inner_min, 3 * accuracy);
				let w = $name::from_rational(inner_min, accuracy / -3);
				let x = $name::from_rational(inner_min, accuracy / 3);

				let y = $name::from_rational(1, accuracy);
				let z = $name::from_rational(1, -accuracy);

				assert_eq!(a.saturating_mul_int(10), 25);
				assert_eq!(b.saturating_mul_int(10),-25);
				assert_eq!(c.saturating_mul_int(10), -25);
				assert_eq!(d.saturating_mul_int(10), 25);

				assert_eq!(e.into_inner(), inner_max);
				assert_eq!(f.into_inner(), inner_min);
				assert_eq!(g.into_inner(), -inner_max);
				assert_eq!(h.into_inner(), inner_max);
				assert_eq!(i.into_inner(), inner_max);

				assert_eq!(j.into_inner(), inner_max);

				assert_eq!(k.into_inner(), inner_max);
				assert_eq!(l.into_inner(), inner_min);
				assert_eq!(n.into_inner(), inner_min);
				assert_eq!(m.into_inner(), inner_max);

				assert_eq!(o.into_inner(), accuracy);
				assert_eq!(p.into_inner(), accuracy);
				assert_eq!(r.into_inner(), -accuracy);
				assert_eq!(s.into_inner(), -accuracy);

				assert_eq!(t.into_inner(), inner_max / 3);
				assert_eq!(u.into_inner(), -inner_max / 3);

				assert_eq!(v.into_inner(), inner_min / 3);
				assert_eq!(w.into_inner(), inner_max);
				assert_eq!(x.into_inner(), inner_min);

				assert_eq!(y.into_inner(), 1);
				assert_eq!(z.into_inner(), -1);

				let a = $name::from_rational(1, accuracy + 1);
				let b = $name::from_rational(1, -accuracy - 1);

				assert_eq!(a.into_inner(), 0);
				assert_eq!(b.into_inner(), 0);
			}

			#[test]
			fn checked_mul_int_works() {
				let a = $name::from_rational(1, 2);
				let b = $name::from_rational(1, -2);
				let c = $name::from_integer(255);

				assert_eq!(a.checked_mul_int(42i128), Some(21));
				assert_eq!(b.checked_mul_int(42i128), Some(-21));
				assert_eq!(c.checked_mul_int(2i128), Some(510));

				assert_eq!(b.checked_mul_int(i128::max_value()), Some(i128::max_value() / -2));
				assert_eq!(b.checked_mul_int(i128::min_value()), Some(i128::min_value() / -2));

				assert_eq!(c.checked_mul_int(i128::max_value()), None);
				assert_eq!(c.checked_mul_int(i128::min_value()), None);

				assert_eq!(a.checked_mul_int(i128::max_value()), Some(i128::max_value() / 2));
				assert_eq!(a.checked_mul_int(u64::max_value()), Some(u64::max_value() / 2));
				assert_eq!(a.checked_mul_int(i128::min_value()), Some(i128::min_value() / 2));
			}

			#[test]
			fn checked_div_int_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				let a = $name::from_inner(inner_max);
				let b = $name::from_inner(inner_min);
				let c = $name::zero();
				let d = $name::one();
				let e = $name::from_integer(6);
				let f = $name::from_integer(5);

				assert_eq!(e.checked_div_int(2.into()), Some(3));
				assert_eq!(f.checked_div_int(2.into()), Some(2));

				assert_eq!(a.checked_div_int(i128::max_value()), Some(0));
				assert_eq!(a.checked_div_int(2), Some(inner_max / (2 * accuracy)));
				assert_eq!(a.checked_div_int(inner_max / accuracy), Some(1));
				assert_eq!(a.checked_div_int(1i8), None);

				assert_eq!(a.checked_div_int(-2), Some(-inner_max / (2 * accuracy)));
				assert_eq!(a.checked_div_int(inner_max / -accuracy), Some(-1));

				assert_eq!(b.checked_div_int(i128::min_value()), Some(0));
				assert_eq!(b.checked_div_int(2), Some(inner_min / (2 * accuracy)));
				assert_eq!(b.checked_div_int(inner_min / accuracy), Some(1));
				assert_eq!(b.checked_div_int(1i8), None);

				assert_eq!(b.checked_div_int(-2), Some(-(inner_min / (2 * accuracy))));
				assert_eq!(b.checked_div_int(-(inner_min / accuracy)), Some(-1));

				assert_eq!(c.checked_div_int(1), Some(0));
				assert_eq!(c.checked_div_int(i128::max_value()), Some(0));
				assert_eq!(c.checked_div_int(i128::min_value()), Some(0));
				assert_eq!(c.checked_div_int(1i8), Some(0));

				assert_eq!(d.checked_div_int(1), Some(1));
				assert_eq!(d.checked_div_int(i32::max_value()), Some(0));
				assert_eq!(d.checked_div_int(i32::min_value()), Some(0));
				assert_eq!(d.checked_div_int(1i8), Some(1));

				assert_eq!(a.checked_div_int(0), None);
				assert_eq!(b.checked_div_int(0), None);
				assert_eq!(c.checked_div_int(0), None);
				assert_eq!(d.checked_div_int(0), None);
			}

			#[test]
			fn saturating_mul_int_works() {
				let a = $name::from_rational(1, 2);
				let b = $name::from_rational(1, -2);
				let c = $name::from_integer(255);
				let d = $name::from_integer(-1);

				assert_eq!(a.saturating_mul_int(42i32), 21);
				assert_eq!(b.saturating_mul_int(42i32), -21);

				assert_eq!(c.saturating_mul_int(2i8), i8::max_value());
				assert_eq!(c.saturating_mul_int(-2i8), i8::min_value());

				assert_eq!(b.saturating_mul_int(i128::max_value()), i128::max_value() / -2);
				assert_eq!(b.saturating_mul_int(i128::min_value()), i128::min_value() / -2);

				assert_eq!(c.saturating_mul_int(i128::max_value()), i128::max_value());
				assert_eq!(c.saturating_mul_int(i128::min_value()), i128::min_value());

				assert_eq!(a.saturating_mul_int(i128::max_value()), i128::max_value() / 2);
				assert_eq!(a.saturating_mul_int(u64::max_value()), u64::max_value() / 2);
				assert_eq!(a.saturating_mul_int(i128::min_value()), i128::min_value() / 2);

				assert_eq!(d.saturating_mul_int(i8::max_value()), -i8::max_value());
				assert_eq!(d.saturating_mul_int(i8::min_value()), i8::max_value());
			}

			#[test]
			fn saturating_abs_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				assert_eq!($name::from_inner(inner_min).saturating_abs(), $name::max_value());
				assert_eq!($name::from_inner(inner_max).saturating_abs(), $name::max_value());
				assert_eq!($name::zero().saturating_abs(), 0.into());
				assert_eq!($name::from_rational(-1, 2).saturating_abs(), (1, 2).into());
			}

			#[test]
			fn saturating_mul_int_acc_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let accuracy = $name::accuracy();

				assert_eq!($name::zero().saturated_multiply_accumulate(accuracy as u64), accuracy as u64);
				assert_eq!($name::one().saturated_multiply_accumulate(accuracy as u64), 2 * accuracy as u64);
				assert_eq!($name::one().saturated_multiply_accumulate(i128::min_value()), i128::min_value());
			}

			fn saturating_pow_should_work() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				assert_eq!($name::from_integer(2).saturating_pow(0), $name::from_integer(1));
				assert_eq!($name::from_integer(2).saturating_pow(1), $name::from_integer(2));
				assert_eq!($name::from_integer(2).saturating_pow(2), $name::from_integer(4));
				assert_eq!($name::from_integer(2).saturating_pow(3), $name::from_integer(8));
				assert_eq!($name::from_integer(2).saturating_pow(50), $name::from_integer(1125899906842624));

				// Saturating.
				assert_eq!($name::from_integer(2).saturating_pow(68), $name::max_value());

				assert_eq!($name::from_integer(1).saturating_pow(1000), $name::from_integer(1));
				assert_eq!($name::from_integer(-1).saturating_pow(1000), $name::from_integer(1));
				assert_eq!($name::from_integer(-1).saturating_pow(1001), $name::from_integer(-1));
				assert_eq!($name::from_integer(1).saturating_pow(usize::max_value()), $name::from_integer(1));
				assert_eq!($name::from_integer(-1).saturating_pow(usize::max_value()), $name::from_integer(-1));
				assert_eq!($name::from_integer(-1).saturating_pow(usize::max_value() - 1), $name::from_integer(1));

				assert_eq!($name::from_integer(114209).saturating_pow(4), $name::max_value());
				assert_eq!($name::from_integer(114209).saturating_pow(5), $name::max_value());

				assert_eq!($name::from_integer(1).saturating_pow(usize::max_value()), $name::from_integer(1));
				assert_eq!($name::from_integer(0).saturating_pow(usize::max_value()), $name::from_integer(0));
				assert_eq!($name::from_integer(2).saturating_pow(usize::max_value()), $name::max_value());
			}

			#[test]
			fn checked_div_works() {
				let inner_max = <$name as FixedPointNumber>::Inner::max_value();
				let inner_min = <$name as FixedPointNumber>::Inner::min_value();
				let accuracy = $name::accuracy();

				let a = $name::from_inner(inner_max);
				let b = $name::from_inner(inner_min);
				let c = $name::zero();
				let d = $name::one();
				let e = $name::from_integer(6);
				let f = $name::from_integer(5);

				assert_eq!(e.checked_div(&2.into()), Some(3.into()));
				assert_eq!(f.checked_div(&2.into()), Some((5, 2).into()));

				assert_eq!(a.checked_div(&inner_max.into()), Some(1.into()));
				assert_eq!(a.checked_div(&2.into()), Some($name::from_inner(inner_max / 2)));
				assert_eq!(a.checked_div(&$name::max_value()), Some(1.into()));
				assert_eq!(a.checked_div(&d), Some(a));

				assert_eq!(a.checked_div(&(-2).into()), Some($name::from_inner(-inner_max / 2)));
				assert_eq!(a.checked_div(&-$name::max_value()), Some((-1).into()));

				assert_eq!(b.checked_div(&b), Some($name::one()));
				assert_eq!(b.checked_div(&2.into()), Some($name::from_inner(inner_min / 2)));

				assert_eq!(b.checked_div(&(-2).into()), Some($name::from_inner(inner_min / -2)));
				assert_eq!(b.checked_div(&-b), Some((-1).into()));

				assert_eq!(c.checked_div(&1.into()), Some(0.into()));
				assert_eq!(c.checked_div(&$name::max_value()), Some(0.into()));
				assert_eq!(c.checked_div(&$name::min_value()), Some(0.into()));

				assert_eq!(d.checked_div(&1.into()), Some(1.into()));
				assert_eq!(d.checked_div(&$name::max_value()), Some(0.into()));
				assert_eq!(d.checked_div(&$name::min_value()), Some(0.into()));

				assert_eq!(a.checked_div(&$name::one()), Some(a));
				assert_eq!(b.checked_div(&$name::one()), Some(b));
				assert_eq!(c.checked_div(&$name::one()), Some(c));
				assert_eq!(d.checked_div(&$name::one()), Some(d));

				assert_eq!(a.checked_div(&$name::zero()), None);
				assert_eq!(b.checked_div(&$name::zero()), None);
				assert_eq!(c.checked_div(&$name::zero()), None);
				assert_eq!(d.checked_div(&$name::zero()), None);
			}

			#[test]
			fn checked_mul_works() {
				let a = $name::from_rational(1, 2);
				let b = $name::from_rational(1, -2);
				let c = $name::from_integer(255);

				assert_eq!(a.checked_mul(&42.into()), Some(21.into()));
				assert_eq!(b.checked_mul(&42.into()), Some((-21).into()));
				assert_eq!(c.checked_mul(&2.into()), Some(510.into()));

				assert_eq!(b.checked_mul(&$name::max_value()), $name::max_value().checked_div(&(-2).into()));
				assert_eq!(b.checked_mul(&$name::min_value()), $name::min_value().checked_div(&(-2).into()));

				assert_eq!(c.checked_mul(&$name::max_value()), None);
				assert_eq!(c.checked_mul(&$name::min_value()), None);

				assert_eq!(a.checked_mul(&$name::max_value()), $name::max_value().checked_div(&2.into()));
				assert_eq!(a.checked_mul(&$name::min_value()), $name::min_value().checked_div(&2.into()));
			} 

			#[test]
			fn mul_works() {
				let a = $name::from_integer(1);
				let b = $name::from_integer(2);
				let c = a * b;
				assert_eq!(c, b);
			}
		}
	}
}