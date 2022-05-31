// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

use crate::traits::{
	BaseArithmetic, Bounded, CheckedAdd, CheckedMul, CheckedSub, One, SaturatedConversion,
	Saturating, UniqueSaturatedInto, Unsigned, Zero,
};
use codec::{CompactAs, Encode};
use num_traits::{Pow, SaturatingAdd, SaturatingSub};
use sp_std::{
	fmt, ops,
	ops::{Add, AddAssign, Div, Rem, Sub},
	prelude::*,
};

/// Get the inner type of a `PerThing`.
pub type InnerOf<P> = <P as PerThing>::Inner;

/// Get the upper type of a `PerThing`.
pub type UpperOf<P> = <P as PerThing>::Upper;

/// Something that implements a fixed point ration with an arbitrary granularity `X`, as _parts per
/// `X`_.
pub trait PerThing:
	Sized
	+ Saturating
	+ Copy
	+ Default
	+ Eq
	+ PartialEq
	+ Ord
	+ PartialOrd
	+ Bounded
	+ fmt::Debug
	+ ops::Div<Output = Self>
	+ ops::Mul<Output = Self>
	+ Pow<usize, Output = Self>
{
	/// The data type used to build this per-thingy.
	type Inner: BaseArithmetic + Unsigned + Copy + Into<u128> + fmt::Debug;

	/// A data type larger than `Self::Inner`, used to avoid overflow in some computations.
	/// It must be able to compute `ACCURACY^2`.
	type Upper: BaseArithmetic
		+ Copy
		+ From<Self::Inner>
		+ TryInto<Self::Inner>
		+ UniqueSaturatedInto<Self::Inner>
		+ Unsigned
		+ fmt::Debug;

	/// The accuracy of this type.
	const ACCURACY: Self::Inner;

	/// Equivalent to `Self::from_parts(0)`.
	fn zero() -> Self {
		Self::from_parts(Self::Inner::zero())
	}

	/// Return `true` if this is nothing.
	fn is_zero(&self) -> bool {
		self.deconstruct() == Self::Inner::zero()
	}

	/// Equivalent to `Self::from_parts(Self::ACCURACY)`.
	fn one() -> Self {
		Self::from_parts(Self::ACCURACY)
	}

	/// Return `true` if this is one.
	fn is_one(&self) -> bool {
		self.deconstruct() == Self::ACCURACY
	}

	/// Return the next lower value to `self` or `self` if it is already zero.
	fn less_epsilon(self) -> Self {
		if self.is_zero() {
			return self
		}
		Self::from_parts(self.deconstruct() - One::one())
	}

	/// Return the next lower value to `self` or an error with the same value if `self` is already
	/// zero.
	fn try_less_epsilon(self) -> Result<Self, Self> {
		if self.is_zero() {
			return Err(self)
		}
		Ok(Self::from_parts(self.deconstruct() - One::one()))
	}

	/// Return the next higher value to `self` or `self` if it is already one.
	fn plus_epsilon(self) -> Self {
		if self.is_one() {
			return self
		}
		Self::from_parts(self.deconstruct() + One::one())
	}

	/// Return the next higher value to `self` or an error with the same value if `self` is already
	/// one.
	fn try_plus_epsilon(self) -> Result<Self, Self> {
		if self.is_one() {
			return Err(self)
		}
		Ok(Self::from_parts(self.deconstruct() + One::one()))
	}

	/// Build this type from a percent. Equivalent to `Self::from_parts(x * Self::ACCURACY / 100)`
	/// but more accurate and can cope with potential type overflows.
	fn from_percent(x: Self::Inner) -> Self {
		let a: Self::Inner = x.min(100.into());
		let b: Self::Inner = 100.into();
		Self::from_rational::<Self::Inner>(a, b)
	}

	/// Return the product of multiplication of this value by itself.
	fn square(self) -> Self {
		let p = Self::Upper::from(self.deconstruct());
		let q = Self::Upper::from(Self::ACCURACY);
		Self::from_rational::<Self::Upper>(p * p, q * q)
	}

	/// Return the part left when `self` is saturating-subtracted from `Self::one()`.
	fn left_from_one(self) -> Self {
		Self::one().saturating_sub(self)
	}

	/// Multiplication that always rounds down to a whole number. The standard `Mul` rounds to the
	/// nearest whole number.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// // round to nearest
	/// assert_eq!(Percent::from_percent(34) * 10u64, 3);
	/// assert_eq!(Percent::from_percent(36) * 10u64, 4);
	///
	/// // round down
	/// assert_eq!(Percent::from_percent(34).mul_floor(10u64), 3);
	/// assert_eq!(Percent::from_percent(36).mul_floor(10u64), 3);
	/// # }
	/// ```
	fn mul_floor<N>(self, b: N) -> N
	where
		N: Clone
			+ UniqueSaturatedInto<Self::Inner>
			+ ops::Rem<N, Output = N>
			+ ops::Div<N, Output = N>
			+ ops::Mul<N, Output = N>
			+ ops::Add<N, Output = N>
			+ Unsigned,
		Self::Inner: Into<N>,
	{
		overflow_prune_mul::<N, Self>(b, self.deconstruct(), Rounding::Down)
	}

	/// Multiplication that always rounds the result up to a whole number. The standard `Mul`
	/// rounds to the nearest whole number.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// // round to nearest
	/// assert_eq!(Percent::from_percent(34) * 10u64, 3);
	/// assert_eq!(Percent::from_percent(36) * 10u64, 4);
	///
	/// // round up
	/// assert_eq!(Percent::from_percent(34).mul_ceil(10u64), 4);
	/// assert_eq!(Percent::from_percent(36).mul_ceil(10u64), 4);
	/// # }
	/// ```
	fn mul_ceil<N>(self, b: N) -> N
	where
		N: Clone
			+ UniqueSaturatedInto<Self::Inner>
			+ ops::Rem<N, Output = N>
			+ ops::Div<N, Output = N>
			+ ops::Mul<N, Output = N>
			+ ops::Add<N, Output = N>
			+ Unsigned,
		Self::Inner: Into<N>,
	{
		overflow_prune_mul::<N, Self>(b, self.deconstruct(), Rounding::Up)
	}

	/// Saturating multiplication by the reciprocal of `self`.	The result is rounded to the
	/// nearest whole number and saturates at the numeric bounds instead of overflowing.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// assert_eq!(Percent::from_percent(50).saturating_reciprocal_mul(10u64), 20);
	/// # }
	/// ```
	fn saturating_reciprocal_mul<N>(self, b: N) -> N
	where
		N: Clone
			+ UniqueSaturatedInto<Self::Inner>
			+ ops::Rem<N, Output = N>
			+ ops::Div<N, Output = N>
			+ ops::Mul<N, Output = N>
			+ ops::Add<N, Output = N>
			+ Saturating
			+ Unsigned,
		Self::Inner: Into<N>,
	{
		saturating_reciprocal_mul::<N, Self>(b, self.deconstruct(), Rounding::NearestPrefUp)
	}

	/// Saturating multiplication by the reciprocal of `self`.	The result is rounded down to the
	/// nearest whole number and saturates at the numeric bounds instead of overflowing.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// // round to nearest
	/// assert_eq!(Percent::from_percent(60).saturating_reciprocal_mul(10u64), 17);
	/// // round down
	/// assert_eq!(Percent::from_percent(60).saturating_reciprocal_mul_floor(10u64), 16);
	/// # }
	/// ```
	fn saturating_reciprocal_mul_floor<N>(self, b: N) -> N
	where
		N: Clone
			+ UniqueSaturatedInto<Self::Inner>
			+ ops::Rem<N, Output = N>
			+ ops::Div<N, Output = N>
			+ ops::Mul<N, Output = N>
			+ ops::Add<N, Output = N>
			+ Saturating
			+ Unsigned,
		Self::Inner: Into<N>,
	{
		saturating_reciprocal_mul::<N, Self>(b, self.deconstruct(), Rounding::Down)
	}

	/// Saturating multiplication by the reciprocal of `self`.	The result is rounded up to the
	/// nearest whole number and saturates at the numeric bounds instead of overflowing.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// // round to nearest
	/// assert_eq!(Percent::from_percent(61).saturating_reciprocal_mul(10u64), 16);
	/// // round up
	/// assert_eq!(Percent::from_percent(61).saturating_reciprocal_mul_ceil(10u64), 17);
	/// # }
	/// ```
	fn saturating_reciprocal_mul_ceil<N>(self, b: N) -> N
	where
		N: Clone
			+ UniqueSaturatedInto<Self::Inner>
			+ ops::Rem<N, Output = N>
			+ ops::Div<N, Output = N>
			+ ops::Mul<N, Output = N>
			+ ops::Add<N, Output = N>
			+ Saturating
			+ Unsigned,
		Self::Inner: Into<N>,
	{
		saturating_reciprocal_mul::<N, Self>(b, self.deconstruct(), Rounding::Up)
	}

	/// Consume self and return the number of parts per thing.
	fn deconstruct(self) -> Self::Inner;

	/// Build this type from a number of parts per thing.
	fn from_parts(parts: Self::Inner) -> Self;

	/// Converts a fraction into `Self`.
	#[cfg(feature = "std")]
	fn from_float(x: f64) -> Self;

	/// Same as `Self::from_float`.
	#[deprecated = "Use from_float instead"]
	#[cfg(feature = "std")]
	fn from_fraction(x: f64) -> Self {
		Self::from_float(x)
	}

	/// Approximate the fraction `p/q` into a per-thing fraction. This will never overflow.
	///
	/// The computation of this approximation is performed in the generic type `N`. Given
	/// `M` as the data type that can hold the maximum value of this per-thing (e.g. u32 for
	/// perbill), this can only work if `N == M` or `N: From<M> + TryInto<M>`.
	///
	/// Note that this always rounds _down_, i.e.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing};
	/// # fn main () {
	/// // 989/1000 is technically closer to 99%.
	/// assert_eq!(
	/// 	Percent::from_rational(989u64, 1000),
	/// 	Percent::from_parts(98),
	/// );
	/// # }
	/// ```
	fn from_rational<N>(p: N, q: N) -> Self
	where
		N: Clone
			+ Ord
			+ TryInto<Self::Inner>
			+ TryInto<Self::Upper>
			+ ops::Div<N, Output = N>
			+ ops::Rem<N, Output = N>
			+ ops::Add<N, Output = N>
			+ ops::AddAssign<N>
			+ Unsigned
			+ Zero
			+ One,
		Self::Inner: Into<N>,
	{
		Self::from_rational_with_rounding(p, q, Rounding::Down).unwrap_or_else(|_| Self::one())
	}

	/// Approximate the fraction `p/q` into a per-thing fraction.
	///
	/// The computation of this approximation is performed in the generic type `N`. Given
	/// `M` as the data type that can hold the maximum value of this per-thing (e.g. `u32` for
	/// `Perbill`), this can only work if `N == M` or `N: From<M> + TryInto<M>`.
	///
	/// In the case of an overflow (or divide by zero), an `Err` is returned.
	///
	/// Rounding is determined by the parameter `rounding`, i.e.
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing, Rounding::*};
	/// # fn main () {
	/// // 989/100 is technically closer to 99%.
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(989u64, 1000, Down).unwrap(),
	/// 	Percent::from_parts(98),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(984u64, 1000, NearestPrefUp).unwrap(),
	/// 	Percent::from_parts(98),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(985u64, 1000, NearestPrefDown).unwrap(),
	/// 	Percent::from_parts(98),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(985u64, 1000, NearestPrefUp).unwrap(),
	/// 	Percent::from_parts(99),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(986u64, 1000, NearestPrefDown).unwrap(),
	/// 	Percent::from_parts(99),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(981u64, 1000, Up).unwrap(),
	/// 	Percent::from_parts(99),
	/// );
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(1001u64, 1000, Up),
	/// 	Err(()),
	/// );
	/// # }
	/// ```
	///
	/// ```rust
	/// # use sp_arithmetic::{Percent, PerThing, Rounding::*};
	/// # fn main () {
	/// assert_eq!(
	/// 	Percent::from_rational_with_rounding(981u64, 1000, Up).unwrap(),
	/// 	Percent::from_parts(99),
	/// );
	/// # }
	/// ```
	fn from_rational_with_rounding<N>(p: N, q: N, rounding: Rounding) -> Result<Self, ()>
	where
		N: Clone
			+ Ord
			+ TryInto<Self::Inner>
			+ TryInto<Self::Upper>
			+ ops::Div<N, Output = N>
			+ ops::Rem<N, Output = N>
			+ ops::Add<N, Output = N>
			+ ops::AddAssign<N>
			+ Unsigned
			+ Zero
			+ One,
		Self::Inner: Into<N>;

	/// Same as `Self::from_rational`.
	#[deprecated = "Use from_rational instead"]
	fn from_rational_approximation<N>(p: N, q: N) -> Self
	where
		N: Clone
			+ Ord
			+ TryInto<Self::Inner>
			+ TryInto<Self::Upper>
			+ ops::Div<N, Output = N>
			+ ops::Rem<N, Output = N>
			+ ops::Add<N, Output = N>
			+ ops::AddAssign<N>
			+ Unsigned
			+ Zero
			+ One,
		Self::Inner: Into<N>,
	{
		Self::from_rational(p, q)
	}
}

/// The rounding method to use for unsigned quantities.
#[derive(Copy, Clone, sp_std::fmt::Debug)]
pub enum Rounding {
	// Towards infinity.
	Up,
	// Towards zero.
	Down,
	// Nearest integer, rounding as `Up` when equidistant.
	NearestPrefUp,
	// Nearest integer, rounding as `Down` when equidistant.
	NearestPrefDown,
}

/// The rounding method to use.
#[derive(Copy, Clone, sp_std::fmt::Debug)]
pub enum SignedRounding {
	// Towards positive infinity.
	High,
	// Towards negative infinity.
	Low,
	// Nearest integer, rounding as `High` when exactly equidistant.
	NearestPrefHigh,
	// Nearest integer, rounding as `Low` when exactly equidistant.
	NearestPrefLow,
	// Away from zero (up when positive, down when negative). When positive, equivalent to `High`.
	Major,
	// Towards zero (down when positive, up when negative). When positive, equivalent to `Low`.
	Minor,
	// Nearest integer, rounding as `Major` when exactly equidistant.
	NearestPrefMajor,
	// Nearest integer, rounding as `Minor` when exactly equidistant.
	NearestPrefMinor,
}

impl Rounding {
	/// Returns the value for `Rounding` which would give the same result ignorant of the sign.
	pub const fn from_signed(rounding: SignedRounding, negative: bool) -> Self {
		use Rounding::*;
		use SignedRounding::*;
		match (rounding, negative) {
			(Low, true) | (Major, _) | (High, false) => Up,
			(High, true) | (Minor, _) | (Low, false) => Down,
			(NearestPrefMajor, _) | (NearestPrefHigh, false) | (NearestPrefLow, true) =>
				NearestPrefUp,
			(NearestPrefMinor, _) | (NearestPrefLow, false) | (NearestPrefHigh, true) =>
				NearestPrefDown,
		}
	}
}

/// Saturating reciprocal multiplication. Compute `x / self`, saturating at the numeric
/// bounds instead of overflowing.
fn saturating_reciprocal_mul<N, P>(x: N, part: P::Inner, rounding: Rounding) -> N
where
	N: Clone
		+ UniqueSaturatedInto<P::Inner>
		+ ops::Div<N, Output = N>
		+ ops::Mul<N, Output = N>
		+ ops::Add<N, Output = N>
		+ ops::Rem<N, Output = N>
		+ Saturating
		+ Unsigned,
	P: PerThing,
	P::Inner: Into<N>,
{
	let maximum: N = P::ACCURACY.into();
	let c = rational_mul_correction::<N, P>(x.clone(), P::ACCURACY, part, rounding);
	(x / part.into()).saturating_mul(maximum).saturating_add(c)
}

/// Overflow-prune multiplication. Accurately multiply a value by `self` without overflowing.
fn overflow_prune_mul<N, P>(x: N, part: P::Inner, rounding: Rounding) -> N
where
	N: Clone
		+ UniqueSaturatedInto<P::Inner>
		+ ops::Div<N, Output = N>
		+ ops::Mul<N, Output = N>
		+ ops::Add<N, Output = N>
		+ ops::Rem<N, Output = N>
		+ Unsigned,
	P: PerThing,
	P::Inner: Into<N>,
{
	let maximum: N = P::ACCURACY.into();
	let part_n: N = part.into();
	let c = rational_mul_correction::<N, P>(x.clone(), part, P::ACCURACY, rounding);
	(x / maximum) * part_n + c
}

/// Compute the error due to integer division in the expression `x / denom * numer`.
///
/// Take the remainder of `x / denom` and multiply by  `numer / denom`. The result can be added
/// to `x / denom * numer` for an accurate result.
fn rational_mul_correction<N, P>(x: N, numer: P::Inner, denom: P::Inner, rounding: Rounding) -> N
where
	N: UniqueSaturatedInto<P::Inner>
		+ ops::Div<N, Output = N>
		+ ops::Mul<N, Output = N>
		+ ops::Add<N, Output = N>
		+ ops::Rem<N, Output = N>
		+ Unsigned,
	P: PerThing,
	P::Inner: Into<N>,
{
	let numer_upper = P::Upper::from(numer);
	let denom_n: N = denom.into();
	let denom_upper = P::Upper::from(denom);
	let rem = x.rem(denom_n);
	// `rem` is less than `denom`, which fits in `P::Inner`.
	let rem_inner = rem.saturated_into::<P::Inner>();
	// `P::Upper` always fits `P::Inner::max_value().pow(2)`, thus it fits `rem * numer`.
	let rem_mul_upper = P::Upper::from(rem_inner) * numer_upper;
	// `rem` is less than `denom`, so `rem * numer / denom` is less than `numer`, which fits in
	// `P::Inner`.
	let mut rem_mul_div_inner = (rem_mul_upper / denom_upper).saturated_into::<P::Inner>();
	match rounding {
		// Already rounded down
		Rounding::Down => {},
		// Round up if the fractional part of the result is non-zero.
		Rounding::Up => {
			if rem_mul_upper % denom_upper > 0.into() {
				// `rem * numer / denom` is less than `numer`, so this will not overflow.
				rem_mul_div_inner += 1.into();
			}
		},
		Rounding::NearestPrefDown =>
			if rem_mul_upper % denom_upper > denom_upper / 2.into() {
				// `rem * numer / denom` is less than `numer`, so this will not overflow.
				rem_mul_div_inner += 1.into();
			},
		Rounding::NearestPrefUp =>
			if rem_mul_upper % denom_upper >= denom_upper / 2.into() + denom_upper % 2.into() {
				// `rem * numer / denom` is less than `numer`, so this will not overflow.
				rem_mul_div_inner += 1.into();
			},
	}
	rem_mul_div_inner.into()
}

/// Just a simple generic integer divide with custom rounding.
fn div_rounded<N>(n: N, d: N, r: Rounding) -> N
where
	N: Clone
		+ Eq
		+ Ord
		+ Zero
		+ One
		+ AddAssign
		+ Add<Output = N>
		+ Rem<Output = N>
		+ Div<Output = N>,
{
	let mut o = n.clone() / d.clone();
	use Rounding::*;
	let two = || N::one() + N::one();
	if match r {
		Up => !((n % d).is_zero()),
		NearestPrefDown => {
			let rem = n % d.clone();
			rem > d / two()
		},
		NearestPrefUp => {
			let rem = n % d.clone();
			rem >= d.clone() / two() + d % two()
		},
		Down => false,
	} {
		o += N::one()
	}
	o
}

macro_rules! implement_per_thing {
	(
		$name:ident,
		$test_mod:ident,
		[$($test_units:tt),+],
		$max:tt,
		$type:ty,
		$upper_type:ty,
		$title:expr $(,)?
	) => {
		/// A fixed point representation of a number in the range [0, 1].
		///
		#[doc = $title]
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
		#[derive(Encode, Copy, Clone, PartialEq, Eq, codec::MaxEncodedLen, PartialOrd, Ord, scale_info::TypeInfo)]
		pub struct $name($type);

		/// Implementation makes any compact encoding of `PerThing::Inner` valid,
		/// when decoding it will saturate up to `PerThing::ACCURACY`.
		impl CompactAs for $name {
			type As = $type;
			fn encode_as(&self) -> &Self::As {
				&self.0
			}
			fn decode_from(x: Self::As) -> Result<Self, codec::Error> {
				// Saturates if `x` is more than `$max` internally.
				Ok(Self::from_parts(x))
			}
		}

		impl From<codec::Compact<$name>> for $name {
			fn from(x: codec::Compact<$name>) -> $name {
				x.0
			}
		}

		#[cfg(feature = "std")]
		impl sp_std::fmt::Debug for $name {
			fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
				if $max == <$type>::max_value() {
					// Not a power of ten: show as N/D and approx %
					let pc = (self.0 as f64) / (self.0 as f64) * 100f64;
					write!(fmt, "{:.2}% ({}/{})", pc, self.0, $max)
				} else {
					// A power of ten: calculate exact percent
					let units = self.0 / ($max / 100);
					let rest = self.0 % ($max / 100);
					write!(fmt, "{}", units)?;
					if rest > 0 {
						write!(fmt, ".")?;
						let mut m = $max / 100;
						while rest % m > 0 {
							m /= 10;
							write!(fmt, "{:01}", rest / m % 10)?;
						}
					}
					write!(fmt, "%")
				}
			}
		}

		#[cfg(not(feature = "std"))]
		impl sp_std::fmt::Debug for $name {
			fn fmt(&self, fmt: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
				if $max == <$type>::max_value() {
					// Not a power of ten: show as N/D and approx %
					write!(fmt, "{}/{}", self.0, $max)
				} else {
					// A power of ten: calculate exact percent
					let units = self.0 / ($max / 100);
					let rest = self.0 % ($max / 100);
					write!(fmt, "{}", units)?;
					if rest > 0 {
						write!(fmt, ".")?;
						let mut m = $max / 100;
						while rest % m > 0 {
							m /= 10;
							write!(fmt, "{:01}", rest / m % 10)?;
						}
					}
					write!(fmt, "%")
				}
			}
		}

		impl PerThing for $name {
			type Inner = $type;
			type Upper = $upper_type;

			const ACCURACY: Self::Inner = $max;

			/// Consume self and return the number of parts per thing.
			fn deconstruct(self) -> Self::Inner { self.0 }

			/// Build this type from a number of parts per thing.
			fn from_parts(parts: Self::Inner) -> Self { Self(parts.min($max)) }

			/// NOTE: saturate to 0 or 1 if x is beyond `[0, 1]`
			#[cfg(feature = "std")]
			fn from_float(x: f64) -> Self {
				Self::from_parts((x.max(0.).min(1.) * $max as f64) as Self::Inner)
			}

			fn from_rational_with_rounding<N>(p: N, q: N, r: Rounding) -> Result<Self, ()>
			where
				N: Clone
					+ Ord
					+ TryInto<Self::Inner>
					+ TryInto<Self::Upper>
					+ ops::Div<N, Output = N>
					+ ops::Rem<N, Output = N>
					+ ops::Add<N, Output = N>
					+ ops::AddAssign<N>
					+ Unsigned
					+ Zero
					+ One,
				Self::Inner: Into<N>
			{
				// q cannot be zero.
				if q.is_zero() { return Err(()) }
				// p should not be bigger than q.
				if p > q { return Err(()) }

				let factor = div_rounded::<N>(q.clone(), $max.into(), Rounding::Up).max(One::one());

				// q cannot overflow: (q / (q/$max)) < $max. p < q hence p also cannot overflow.
				let q_reduce: $type = div_rounded(q, factor.clone(), r)
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"`q / ceil(q/$max) < $max`; macro prevents any type being created that \
						does not satisfy this; qed"
					);
				let p_reduce: $type = div_rounded(p, factor, r)
					.try_into()
					.map_err(|_| "Failed to convert")
					.expect(
						"`p / ceil(p/$max) < $max`; macro prevents any type being created that \
						does not satisfy this; qed"
					);

				// `p_reduced` and `q_reduced` are within `Self::Inner`. Multiplication by another
				// `$max` will always fit in `$upper_type`. This is guaranteed by the macro tests.
				let n = p_reduce as $upper_type * <$upper_type>::from($max);
				let d = q_reduce as $upper_type;
				let part = div_rounded(n, d, r);
				Ok($name(part as Self::Inner))
			}
		}

		impl $name {
			/// From an explicitly defined number of parts per maximum of the type.
			///
			// needed only for peru16. Since peru16 is the only type in which $max ==
			// $type::max_value(), rustc is being a smart-a** here by warning that the comparison
			// is not needed.
			#[allow(unused_comparisons)]
			pub const fn from_parts(parts: $type) -> Self {
				Self([parts, $max][(parts > $max) as usize])
			}

			/// Converts a percent into `Self`. Equal to `x / 100`.
			///
			/// This can be created at compile time.
			pub const fn from_percent(x: $type) -> Self {
				Self(([x, 100][(x > 100) as usize] as $upper_type * $max as $upper_type / 100) as $type)
			}

			/// See [`PerThing::one`]
			pub const fn one() -> Self {
				Self::from_parts($max)
			}

			/// See [`PerThing::is_one`].
			pub fn is_one(&self) -> bool {
				PerThing::is_one(self)
			}

			/// See [`PerThing::zero`].
			pub const fn zero() -> Self {
				Self::from_parts(0)
			}

			/// See [`PerThing::is_zero`].
			pub fn is_zero(&self) -> bool {
				PerThing::is_zero(self)
			}

			/// See [`PerThing::deconstruct`].
			pub const fn deconstruct(self) -> $type {
				self.0
			}

			/// See [`PerThing::square`].
			pub fn square(self) -> Self {
				PerThing::square(self)
			}

			/// See [`PerThing::from_float`].
			#[cfg(feature = "std")]
			pub fn from_float(x: f64) -> Self {
				<Self as PerThing>::from_float(x)
			}

			/// See [`PerThing::from_rational`].
			#[deprecated = "Use `PerThing::from_rational` instead"]
			pub fn from_rational_approximation<N>(p: N, q: N) -> Self
			where
				N: Clone
					+ Ord
					+ TryInto<$type>
					+ TryInto<$upper_type>
					+ ops::Div<N, Output = N>
					+ ops::Rem<N, Output = N>
					+ ops::Add<N, Output = N>
					+ ops::AddAssign<N>
					+ Unsigned
					+ Zero
					+ One,
				$type: Into<N>
			{
				<Self as PerThing>::from_rational(p, q)
			}

			/// See [`PerThing::from_rational`].
			pub fn from_rational<N>(p: N, q: N) -> Self
			where
				N: Clone
					+ Ord
					+ TryInto<$type>
					+ TryInto<$upper_type>
					+ ops::Div<N, Output = N>
					+ ops::Rem<N, Output = N>
					+ ops::Add<N, Output = N>
					+ ops::AddAssign<N>
					+ Unsigned
					+ Zero
					+ One,
				$type: Into<N>
			{
				<Self as PerThing>::from_rational(p, q)
			}

			/// Integer multiplication with another value, saturating at 1.
			pub fn int_mul(self, b: $type) -> Self {
				PerThing::from_parts(self.0.saturating_mul(b))
			}

			/// Integer division with another value, rounding down.
			pub fn int_div(self, b: Self) -> $type {
				self.0 / b.0
			}

			/// See [`PerThing::mul_floor`].
			pub fn mul_floor<N>(self, b: N) -> N
				where
					N: Clone + UniqueSaturatedInto<$type> +
						ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
						ops::Add<N, Output=N> + Unsigned,
					$type: Into<N>,

			{
				PerThing::mul_floor(self, b)
			}

			/// See [`PerThing::mul_ceil`].
			pub fn mul_ceil<N>(self, b: N) -> N
				where
					N: Clone + UniqueSaturatedInto<$type> +
						ops::Rem<N, Output=N> + ops::Div<N, Output=N> + ops::Mul<N, Output=N> +
						ops::Add<N, Output=N> + Unsigned,
					$type: Into<N>,
			{
				PerThing::mul_ceil(self, b)
			}

			/// See [`PerThing::saturating_reciprocal_mul`].
			pub fn saturating_reciprocal_mul<N>(self, b: N) -> N
				where
					N: Clone + UniqueSaturatedInto<$type> + ops::Rem<N, Output=N> +
						ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> +
						Saturating + Unsigned,
					$type: Into<N>,
			{
				PerThing::saturating_reciprocal_mul(self, b)
			}

			/// See [`PerThing::saturating_reciprocal_mul_floor`].
			pub fn saturating_reciprocal_mul_floor<N>(self, b: N) -> N
				where
					N: Clone + UniqueSaturatedInto<$type> + ops::Rem<N, Output=N> +
						ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> +
						Saturating + Unsigned,
					$type: Into<N>,
			{
				PerThing::saturating_reciprocal_mul_floor(self, b)
			}

			/// See [`PerThing::saturating_reciprocal_mul_ceil`].
			pub fn saturating_reciprocal_mul_ceil<N>(self, b: N) -> N
				where
					N: Clone + UniqueSaturatedInto<$type> + ops::Rem<N, Output=N> +
						ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> +
						Saturating + Unsigned,
					$type: Into<N>,
			{
				PerThing::saturating_reciprocal_mul_ceil(self, b)
			}

			/// Saturating division. Compute `self / rhs`, saturating at one if `rhs < self`.
			///
			/// The `rounding` method must be specified. e.g.:
			///
			/// ```rust
			/// # use sp_arithmetic::{Percent, PerThing, Rounding::*};
			/// # fn main () {
			/// let pc = |x| Percent::from_percent(x);
			/// assert_eq!(
			/// 	pc(2).saturating_div(pc(3), Down),
			/// 	pc(66),
			/// );
			/// assert_eq!(
			/// 	pc(1).saturating_div(pc(3), NearestPrefUp),
			/// 	pc(33),
			/// );
			/// assert_eq!(
			/// 	pc(2).saturating_div(pc(3), NearestPrefDown),
			/// 	pc(67),
			/// );
			/// assert_eq!(
			/// 	pc(1).saturating_div(pc(3), Up),
			/// 	pc(34),
			/// );
			/// # }
			/// ```
			pub fn saturating_div(self, rhs: Self, r: Rounding) -> Self {
				let p = self.0;
				let q = rhs.0;
				Self::from_rational_with_rounding(p, q, r).unwrap_or_else(|_| Self::one())
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
				self * rhs
			}

			/// Saturating exponentiation. Computes `self.pow(exp)`, saturating at the numeric
			/// bounds instead of overflowing. This operation is lossy.
			fn saturating_pow(self, exp: usize) -> Self {
				self.pow(exp)
			}
		}

		impl codec::Decode for $name {
			fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
				let inner = <$type as codec::Decode>::decode(input)?;

				if inner <= <Self as PerThing>::ACCURACY {
					Ok(Self(inner))
				} else {
					Err("Value is greater than allowed maximum!".into())
				}
			}
		}

		impl Bounded for $name {
			fn min_value() -> Self {
				<Self as PerThing>::zero()
			}

			fn max_value() -> Self {
				<Self as PerThing>::one()
			}
		}

		impl ops::Mul for $name {
			type Output = Self;

			fn mul(self, rhs: Self) -> Self::Output {
				let a = self.0 as $upper_type;
				let b = rhs.0 as $upper_type;
				let m = <$upper_type>::from($max);
				let parts = a * b / m;
				// This will always fit into $type.
				Self::from_parts(parts as $type)
			}
		}

		impl Pow<usize> for $name {
			type Output = Self;

			fn pow(mut self, exp: usize) -> Self::Output {
				if exp == 0 || self.is_one() {
					return Self::one()
				}

				let mut result = self;
				let mut exp = exp - 1;
				while exp > 0 && !result.is_zero() {
					if exp % 2 != 0 {
						result = result * self;
						exp -= 1;
					}
					self = self.square();
					exp /= 2;
				}
				result
			}
		}

		impl ops::Div for $name {
			type Output = Self;

			fn div(self, rhs: Self) -> Self::Output {
				let p = self.0;
				let q = rhs.0;
				Self::from_rational(p, q)
			}
		}

		impl Default for $name {
			fn default() -> Self {
				<Self as PerThing>::zero()
			}
		}

		/// Non-overflow multiplication.
		///
		/// This is tailored to be used with a balance type.
		impl<N> ops::Mul<N> for $name
		where
			N: Clone + UniqueSaturatedInto<$type> + ops::Rem<N, Output=N>
				+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N> + Unsigned,
			$type: Into<N>,
		{
			type Output = N;
			fn mul(self, b: N) -> Self::Output {
				overflow_prune_mul::<N, Self>(b, self.deconstruct(), Rounding::NearestPrefDown)
			}
		}

		impl<N> ops::Div<N> for $name where $type: TryFrom<N> {
			type Output = Self;
			fn div(self, b: N) -> Self::Output {
				<$type>::try_from(b).map_or(Self::zero(), |d| Self::from_parts(self.0 / d))
			}
		}

		impl Add<Self> for $name {
			type Output = $name;

			// For PerU16, $max == u16::MAX, so we need this `allow`.
			#[allow(unused_comparisons)]
			#[inline]
			fn add(self, rhs: Self) -> Self::Output {
				let inner = self.deconstruct().add(rhs.deconstruct());
				debug_assert!(inner <= $max);
				$name::from_parts(inner)
			}
		}

		impl CheckedAdd for $name {
			// For PerU16, $max == u16::MAX, so we need this `allow`.
			#[allow(unused_comparisons)]
			#[inline]
			fn checked_add(&self, rhs: &Self) -> Option<Self> {
				self.deconstruct()
					.checked_add(rhs.deconstruct())
					.map(|inner| if inner > $max { None } else { Some($name::from_parts(inner)) })
					.flatten()
			}
		}

		impl Sub<Self> for $name {
			type Output = $name;

			#[inline]
			fn sub(self, rhs: Self) -> Self::Output {
				$name::from_parts(self.deconstruct().sub(rhs.deconstruct()))
			}
		}

		impl CheckedSub for $name {
			#[inline]
			fn checked_sub(&self, v: &Self) -> Option<Self> {
				self.deconstruct().checked_sub(v.deconstruct()).map($name::from_parts)
			}
		}

		impl SaturatingAdd for $name {
			#[inline]
			fn saturating_add(&self, v: &Self) -> Self {
				$name::from_parts(self.deconstruct().saturating_add(v.deconstruct()))
			}
		}

		impl SaturatingSub for $name {
			#[inline]
			fn saturating_sub(&self, v: &Self) -> Self {
				$name::from_parts(self.deconstruct().saturating_sub(v.deconstruct()))
			}
		}

		/// # Note
		/// CheckedMul will never fail for PerThings.
		impl CheckedMul for $name {
			#[inline]
			fn checked_mul(&self, rhs: &Self) -> Option<Self> {
				Some(*self * *rhs)
			}
		}

		impl $crate::traits::Zero for $name {
			fn zero() -> Self {
				Self::zero()
			}

			fn is_zero(&self) -> bool {
				self == &Self::zero()
			}
		}


		#[cfg(test)]
		mod $test_mod {
			use codec::{Encode, Decode};
			use super::{$name, Saturating, PerThing};
			use crate::traits::Zero;

			#[test]
			fn macro_expanded_correctly() {
				// needed for the `from_percent` to work. UPDATE: this is no longer needed; yet note
				// that tests that use percentage or fractions such as $name::from_float(0.2) to
				// create values will most likely be inaccurate when used with per_things that are
				// not multiples of 100.
				// assert!($max >= 100);
				// assert!($max % 100 == 0);

				// needed for `from_rational`
				assert!(2 * ($max as $upper_type) < <$upper_type>::max_value());
				assert!(<$upper_type>::from($max) < <$upper_type>::max_value());

				// for something like percent they can be the same.
				assert!((<$type>::max_value() as $upper_type) <= <$upper_type>::max_value());
				assert!(<$upper_type>::from($max).checked_mul($max.into()).is_some());

				// make sure saturating_pow won't overflow the upper type
				assert!(<$upper_type>::from($max) * <$upper_type>::from($max) < <$upper_type>::max_value());
			}

			#[derive(Encode, Decode, PartialEq, Eq, Debug)]
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
					// (<$type>::max_value(), <$type>::max_value().encode().len() + 1)
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
			fn from_parts_cannot_overflow() {
				assert_eq!(<$name>::from_parts($max.saturating_add(1)), <$name>::one());
			}

			#[test]
			fn has_max_encoded_len() {
				struct AsMaxEncodedLen<T: codec::MaxEncodedLen> {
					_data: T,
				}

				let _ = AsMaxEncodedLen { _data: $name(1) };
			}

			#[test]
			fn fail_on_invalid_encoded_value() {
				let value = <$upper_type>::from($max) * 2;
				let casted = value as $type;
				let encoded = casted.encode();

				// For types where `$max == $type::maximum()` we can not
				if <$upper_type>::from(casted) == value {
					assert_eq!(
						$name::decode(&mut &encoded[..]),
						Err("Value is greater than allowed maximum!".into()),
					);
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
				assert_eq!($name::from_percent(50), $name::from_parts($max / 2));
				assert_eq!($name::from_percent(100), $name::from_parts($max));
				assert_eq!($name::from_percent(200), $name::from_parts($max));

				assert_eq!($name::from_float(0.0), $name::from_parts(Zero::zero()));
				assert_eq!($name::from_float(0.1), $name::from_parts($max / 10));
				assert_eq!($name::from_float(1.0), $name::from_parts($max));
				assert_eq!($name::from_float(2.0), $name::from_parts($max));
				assert_eq!($name::from_float(-1.0), $name::from_parts(Zero::zero()));
			}

			#[test]
			fn percent_trait_impl_works() {
				assert_eq!(<$name as PerThing>::from_percent(0), $name::from_parts(Zero::zero()));
				assert_eq!(<$name as PerThing>::from_percent(10), $name::from_parts($max / 10));
				assert_eq!(<$name as PerThing>::from_percent(50), $name::from_parts($max / 2));
				assert_eq!(<$name as PerThing>::from_percent(100), $name::from_parts($max));
				assert_eq!(<$name as PerThing>::from_percent(200), $name::from_parts($max));
			}

			macro_rules! u256ify {
				($val:expr) => {
					Into::<U256>::into($val)
				};
			}

			macro_rules! per_thing_mul_test {
				($num_type:tt) => {
					// multiplication from all sort of from_percent
					assert_eq!(
						$name::from_float(1.0) * $num_type::max_value(),
						$num_type::max_value()
					);
					if $max % 100 == 0 {
						assert_eq_error_rate!(
							$name::from_percent(99) * $num_type::max_value(),
							((Into::<U256>::into($num_type::max_value()) * 99u32) / 100u32).as_u128() as $num_type,
							1,
						);
						assert_eq!(
							$name::from_float(0.5) * $num_type::max_value(),
							$num_type::max_value() / 2,
						);
						assert_eq_error_rate!(
							$name::from_percent(1) * $num_type::max_value(),
							$num_type::max_value() / 100,
							1,
						);
					} else {
						assert_eq!(
							$name::from_float(0.99) * <$num_type>::max_value(),
							(
								(
									u256ify!($name::from_float(0.99).0) *
									u256ify!(<$num_type>::max_value()) /
									u256ify!($max)
								).as_u128()
							) as $num_type,
						);
						assert_eq!(
							$name::from_float(0.50) * <$num_type>::max_value(),
							(
								(
									u256ify!($name::from_float(0.50).0) *
									u256ify!(<$num_type>::max_value()) /
									u256ify!($max)
								).as_u128()
							) as $num_type,
						);
						assert_eq!(
							$name::from_float(0.01) * <$num_type>::max_value(),
							(
								(
									u256ify!($name::from_float(0.01).0) *
									u256ify!(<$num_type>::max_value()) /
									u256ify!($max)
								).as_u128()
							) as $num_type,
						);
					}

					assert_eq!($name::from_float(0.0) * $num_type::max_value(), 0);

					// // multiplication with bounds
					assert_eq!($name::one() * $num_type::max_value(), $num_type::max_value());
					assert_eq!($name::zero() * $num_type::max_value(), 0);
				}
			}

			#[test]
			fn per_thing_mul_works() {
				use primitive_types::U256;

				// accuracy test
				assert_eq!(
					$name::from_rational(1 as $type, 3) * 30 as $type,
					10,
				);

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
						$name::from_rational(1 as $num_type, 0),
						$name::one(),
					);
					assert_eq!(
						$name::from_rational(1 as $num_type, 1),
						$name::one(),
					);
					assert_eq_error_rate!(
						$name::from_rational(1 as $num_type, 3).0,
						$name::from_parts($max / 3).0,
						2
					);
					assert_eq!(
						$name::from_rational(1 as $num_type, 10),
						$name::from_float(0.10),
					);
					assert_eq!(
						$name::from_rational(1 as $num_type, 4),
						$name::from_float(0.25),
					);
					assert_eq!(
						$name::from_rational(1 as $num_type, 4),
						$name::from_rational(2 as $num_type, 8),
					);
					// no accurate anymore but won't overflow.
					assert_eq_error_rate!(
						$name::from_rational(
							$num_type::max_value() - 1,
							$num_type::max_value()
						).0 as $upper_type,
						$name::one().0 as $upper_type,
						2,
					);
					assert_eq_error_rate!(
						$name::from_rational(
							$num_type::max_value() / 3,
							$num_type::max_value()
						).0 as $upper_type,
						$name::from_parts($max / 3).0 as $upper_type,
						2,
					);
					assert_eq!(
						$name::from_rational(1, $num_type::max_value()),
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
					$name::from_rational(max_value - 1, max_value + 1),
					$name::from_parts($max - 2),
				);
				assert_eq!(
					$name::from_rational(1, $max - 1),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational(1, $max),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational(2, 2 * max_value - 1),
					$name::from_parts(1),
				);
				assert_eq!(
					$name::from_rational(1, max_value + 1),
					$name::zero(),
				);
				assert_eq!(
					$name::from_rational(3 * max_value / 2, 3 * max_value),
					$name::from_float(0.5),
				);

				$(per_thing_from_rationale_approx_test!($test_units);)*
			}

			#[test]
			fn per_things_mul_operates_in_output_type() {
				// assert_eq!($name::from_float(0.5) * 100u32, 50u32);
				assert_eq!($name::from_float(0.5) * 100u64, 50u64);
				assert_eq!($name::from_float(0.5) * 100u128, 50u128);
			}

			#[test]
			fn per_thing_saturating_op_works() {
				assert_eq_error_rate!(
					$name::from_float(0.5).saturating_add($name::from_float(0.4)).0 as $upper_type,
					$name::from_float(0.9).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					$name::from_float(0.5).saturating_add($name::from_float(0.5)).0 as $upper_type,
					$name::one().0 as $upper_type,
					2,
				);
				assert_eq!(
					$name::from_float(0.6).saturating_add($name::from_float(0.5)),
					$name::one(),
				);

				assert_eq_error_rate!(
					$name::from_float(0.6).saturating_sub($name::from_float(0.5)).0 as $upper_type,
					$name::from_float(0.1).0 as $upper_type,
					2,
				);
				assert_eq!(
					$name::from_float(0.6).saturating_sub($name::from_float(0.6)),
					$name::from_float(0.0),
				);
				assert_eq!(
					$name::from_float(0.6).saturating_sub($name::from_float(0.7)),
					$name::from_float(0.0),
				);

				assert_eq_error_rate!(
					$name::from_float(0.5).saturating_mul($name::from_float(0.5)).0 as $upper_type,
					$name::from_float(0.25).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					$name::from_float(0.2).saturating_mul($name::from_float(0.2)).0 as $upper_type,
					$name::from_float(0.04).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					$name::from_float(0.1).saturating_mul($name::from_float(0.1)).0 as $upper_type,
					$name::from_float(0.01).0 as $upper_type,
					1,
				);
			}

			#[test]
			fn per_thing_square_works() {
				assert_eq!($name::from_float(1.0).square(), $name::from_float(1.0));
				assert_eq!($name::from_float(0.5).square(), $name::from_float(0.25));
				assert_eq!($name::from_float(0.1).square(), $name::from_float(0.01));
				assert_eq!(
					$name::from_float(0.02).square(),
					$name::from_parts((4 * <$upper_type>::from($max) / 100 / 100) as $type)
				);
			}

			#[test]
			fn per_things_div_works() {
				// normal
				assert_eq_error_rate!(
					($name::from_float(0.1) / $name::from_float(0.20)).0 as $upper_type,
					$name::from_float(0.50).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					($name::from_float(0.1) / $name::from_float(0.10)).0 as $upper_type,
					$name::from_float(1.0).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					($name::from_float(0.1) / $name::from_float(0.0)).0 as $upper_type,
					$name::from_float(1.0).0 as $upper_type,
					2,
				);

				// will not overflow
				assert_eq_error_rate!(
					($name::from_float(0.10) / $name::from_float(0.05)).0 as $upper_type,
					$name::from_float(1.0).0 as $upper_type,
					2,
				);
				assert_eq_error_rate!(
					($name::from_float(1.0) / $name::from_float(0.5)).0 as $upper_type,
					$name::from_float(1.0).0 as $upper_type,
					2,
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

				// x^2 .. x^16
				for n in 1..=16 {
					assert_eq!(
						$name::from_parts($max / 2).saturating_pow(n),
						$name::from_parts(($max as u128 / 2u128.pow(n as u32)) as $type),
					);
				}

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
					$name::from_parts($max).saturating_reciprocal_mul(<$type>::from(10u8)),
					10,
				);
				// divide by 1/2
				assert_eq!(
					$name::from_parts($max / 2).saturating_reciprocal_mul(<$type>::from(10u8)),
					20,
				);
				// saturate
				assert_eq!(
					$name::from_parts(1).saturating_reciprocal_mul($max),
					<$type>::max_value(),
				);
				// round to nearest
				assert_eq!(
					$name::from_percent(60).saturating_reciprocal_mul(<$type>::from(10u8)),
					17,
				);
				// round down
				assert_eq!(
					$name::from_percent(60).saturating_reciprocal_mul_floor(<$type>::from(10u8)),
					16,
				);
				// round to nearest
				assert_eq!(
					$name::from_percent(61).saturating_reciprocal_mul(<$type>::from(10u8)),
					16,
				);
				// round up
				assert_eq!(
					$name::from_percent(61).saturating_reciprocal_mul_ceil(<$type>::from(10u8)),
					17,
				);
			}

			#[test]
			fn saturating_truncating_mul_works() {
				assert_eq!(
					$name::from_percent(49).mul_floor(10 as $type),
					4,
				);
				let a: $upper_type = $name::from_percent(50).mul_floor(($max as $upper_type).pow(2));
				let b: $upper_type = ($max as $upper_type).pow(2) / 2;
				if $max % 2 == 0 {
					assert_eq!(a, b);
				} else {
					// difference should be less that 1%, IE less than the error in `from_percent`
					assert!(b - a < ($max as $upper_type).pow(2) / 100 as $upper_type);
				}
			}

			#[test]
			fn rational_mul_correction_works() {
				assert_eq!(
					super::rational_mul_correction::<$type, $name>(
						<$type>::max_value(),
						<$type>::max_value(),
						<$type>::max_value(),
						super::Rounding::NearestPrefDown,
					),
					0,
				);
				assert_eq!(
					super::rational_mul_correction::<$type, $name>(
						<$type>::max_value() - 1,
						<$type>::max_value(),
						<$type>::max_value(),
						super::Rounding::NearestPrefDown,
					),
					<$type>::max_value() - 1,
				);
				assert_eq!(
					super::rational_mul_correction::<$upper_type, $name>(
						((<$type>::max_value() - 1) as $upper_type).pow(2),
						<$type>::max_value(),
						<$type>::max_value(),
						super::Rounding::NearestPrefDown,
					),
					1,
				);
				// ((max^2 - 1) % max) * max / max == max - 1
				assert_eq!(
					super::rational_mul_correction::<$upper_type, $name>(
						(<$type>::max_value() as $upper_type).pow(2) - 1,
						<$type>::max_value(),
						<$type>::max_value(),
						super::Rounding::NearestPrefDown,
					),
					<$upper_type>::from((<$type>::max_value() - 1)),
				);
				// (max % 2) * max / 2 == max / 2
				assert_eq!(
					super::rational_mul_correction::<$upper_type, $name>(
						(<$type>::max_value() as $upper_type).pow(2),
						<$type>::max_value(),
						2 as $type,
						super::Rounding::NearestPrefDown,
					),
					<$type>::max_value() as $upper_type / 2,
				);
				// ((max^2 - 1) % max) * 2 / max == 2 (rounded up)
				assert_eq!(
					super::rational_mul_correction::<$upper_type, $name>(
						(<$type>::max_value() as $upper_type).pow(2) - 1,
						2 as $type,
						<$type>::max_value(),
						super::Rounding::NearestPrefDown,
					),
					2,
				);
				// ((max^2 - 1) % max) * 2 / max == 1 (rounded down)
				assert_eq!(
					super::rational_mul_correction::<$upper_type, $name>(
						(<$type>::max_value() as $upper_type).pow(2) - 1,
						2 as $type,
						<$type>::max_value(),
						super::Rounding::Down,
					),
					1,
				);
			}

			#[test]
			#[allow(unused)]
			fn const_fns_work() {
				const C1: $name = $name::from_percent(50);
				const C2: $name = $name::one();
				const C3: $name = $name::zero();
				const C4: $name = $name::from_parts(1);

				// deconstruct is also const, hence it can be called in const rhs.
				const C5: bool = C1.deconstruct() == 0;
			}

			#[test]
			fn compact_decoding_saturate_when_beyond_accuracy() {
				use num_traits::Bounded;
				use codec::Compact;

				let p = Compact::<$name>::decode(&mut &Compact(<$type>::max_value()).encode()[..])
					.unwrap();
				assert_eq!((p.0).0, $max);
				assert_eq!($name::from(p), $name::max_value());
			}

			#[allow(unused_imports)]
			use super::*;

			#[test]
			fn test_add_basic() {
				assert_eq!($name::from_parts(1) + $name::from_parts(1), $name::from_parts(2));
				assert_eq!($name::from_parts(10) + $name::from_parts(10), $name::from_parts(20));
			}

			#[test]
			fn test_basic_checked_add() {
				assert_eq!(
					$name::from_parts(1).checked_add(&$name::from_parts(1)),
					Some($name::from_parts(2))
				);
				assert_eq!(
					$name::from_parts(10).checked_add(&$name::from_parts(10)),
					Some($name::from_parts(20))
				);
				assert_eq!(
					$name::from_parts(<$type>::MAX).checked_add(&$name::from_parts(<$type>::MAX)),
					None
				);
				assert_eq!(
					$name::from_parts($max).checked_add(&$name::from_parts(1)),
					None
				);
			}

			#[test]
			fn test_basic_saturating_add() {
				assert_eq!(
					$name::from_parts(1).saturating_add($name::from_parts(1)),
					$name::from_parts(2)
				);
				assert_eq!(
					$name::from_parts(10).saturating_add($name::from_parts(10)),
					$name::from_parts(20)
				);
				assert_eq!(
					$name::from_parts(<$type>::MAX).saturating_add($name::from_parts(<$type>::MAX)),
					$name::from_parts(<$type>::MAX)
				);
			}

			#[test]
			fn test_basic_sub() {
				assert_eq!($name::from_parts(2) - $name::from_parts(1), $name::from_parts(1));
				assert_eq!($name::from_parts(20) - $name::from_parts(10), $name::from_parts(10));
			}

			#[test]
			fn test_basic_checked_sub() {
				assert_eq!(
					$name::from_parts(2).checked_sub(&$name::from_parts(1)),
					Some($name::from_parts(1))
				);
				assert_eq!(
					$name::from_parts(20).checked_sub(&$name::from_parts(10)),
					Some($name::from_parts(10))
				);
				assert_eq!($name::from_parts(0).checked_sub(&$name::from_parts(1)), None);
			}

			#[test]
			fn test_basic_saturating_sub() {
				assert_eq!(
					$name::from_parts(2).saturating_sub($name::from_parts(1)),
					$name::from_parts(1)
				);
				assert_eq!(
					$name::from_parts(20).saturating_sub($name::from_parts(10)),
					$name::from_parts(10)
				);
				assert_eq!(
					$name::from_parts(0).saturating_sub($name::from_parts(1)),
					$name::from_parts(0)
				);
			}

			#[test]
			fn test_basic_checked_mul() {
				assert_eq!(
					$name::from_parts($max).checked_mul(&$name::from_parts($max)),
					Some($name::from_percent(100))
				);
				assert_eq!(
					$name::from_percent(100).checked_mul(&$name::from_percent(100)),
					Some($name::from_percent(100))
				);
				assert_eq!(
					$name::from_percent(50).checked_mul(&$name::from_percent(26)),
					Some($name::from_percent(13))
				);
				assert_eq!(
					$name::from_percent(0).checked_mul(&$name::from_percent(0)),
					Some($name::from_percent(0))
				);
			}
		}
	};
}

macro_rules! implement_per_thing_with_perthousand {
	(
		$name:ident,
		$test_mod:ident,
		$pt_test_mod:ident,
		[$($test_units:tt),+],
		$max:tt,
		$type:ty,
		$upper_type:ty,
		$title:expr $(,)?
	) => {
		implement_per_thing! {
			$name, $test_mod, [ $( $test_units ),+ ], $max, $type, $upper_type, $title,
		}
		impl $name {
			/// Converts a percent into `Self`. Equal to `x / 1000`.
			///
			/// This can be created at compile time.
			pub const fn from_perthousand(x: $type) -> Self {
				Self(([x, 1000][(x > 1000) as usize] as $upper_type * $max as $upper_type / 1000) as $type)
			}
		}
		#[cfg(test)]
		mod $pt_test_mod {
			use super::$name;
			use crate::traits::Zero;

			#[test]
			fn from_perthousand_works() {
				// some really basic stuff
				assert_eq!($name::from_perthousand(00), $name::from_parts(Zero::zero()));
				assert_eq!($name::from_perthousand(100), $name::from_parts($max / 10));
				assert_eq!($name::from_perthousand(1000), $name::from_parts($max));
				assert_eq!($name::from_perthousand(2000), $name::from_parts($max));
			}

			#[test]
			#[allow(unused)]
			fn const_fns_work() {
				const C1: $name = $name::from_perthousand(500);
			}
		}
	}
}

#[test]
fn from_rational_with_rounding_works_in_extreme_case() {
	use Rounding::*;
	for &r in [Down, NearestPrefDown, NearestPrefUp, Up].iter() {
		Percent::from_rational_with_rounding(1, u64::max_value(), r).unwrap();
		Percent::from_rational_with_rounding(1, u32::max_value(), r).unwrap();
		Percent::from_rational_with_rounding(1, u16::max_value(), r).unwrap();
		Percent::from_rational_with_rounding(u64::max_value() - 1, u64::max_value(), r).unwrap();
		Percent::from_rational_with_rounding(u32::max_value() - 1, u32::max_value(), r).unwrap();
		Percent::from_rational_with_rounding(u16::max_value() - 1, u16::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(1, u64::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(1, u32::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(1, u16::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(u64::max_value() - 1, u64::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(u32::max_value() - 1, u32::max_value(), r).unwrap();
		PerU16::from_rational_with_rounding(u16::max_value() - 1, u16::max_value(), r).unwrap();
		Permill::from_rational_with_rounding(1, u64::max_value(), r).unwrap();
		Permill::from_rational_with_rounding(1, u32::max_value(), r).unwrap();
		Permill::from_rational_with_rounding(u64::max_value() - 1, u64::max_value(), r).unwrap();
		Permill::from_rational_with_rounding(u32::max_value() - 1, u32::max_value(), r).unwrap();
		Perbill::from_rational_with_rounding(1, u64::max_value(), r).unwrap();
		Perbill::from_rational_with_rounding(1, u32::max_value(), r).unwrap();
		Perbill::from_rational_with_rounding(u64::max_value() - 1, u64::max_value(), r).unwrap();
		Perbill::from_rational_with_rounding(u32::max_value() - 1, u32::max_value(), r).unwrap();
	}
}

implement_per_thing!(Percent, test_per_cent, [u32, u64, u128], 100u8, u8, u16, "_Percent_",);
implement_per_thing_with_perthousand!(
	PerU16,
	test_peru16,
	test_peru16_extra,
	[u32, u64, u128],
	65535_u16,
	u16,
	u32,
	"_Parts per 65535_",
);
implement_per_thing_with_perthousand!(
	Permill,
	test_permill,
	test_permill_extra,
	[u32, u64, u128],
	1_000_000u32,
	u32,
	u64,
	"_Parts per Million_",
);
implement_per_thing_with_perthousand!(
	Perbill,
	test_perbill,
	test_perbill_extra,
	[u32, u64, u128],
	1_000_000_000u32,
	u32,
	u64,
	"_Parts per Billion_",
);
implement_per_thing_with_perthousand!(
	Perquintill,
	test_perquintill,
	test_perquintill_extra,
	[u64, u128],
	1_000_000_000_000_000_000u64,
	u64,
	u128,
	"_Parts per Quintillion_",
);
