// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Primitive traits for the runtime arithmetic.

use sp_std::{self, convert::{TryFrom, TryInto}, fmt::Debug};
use codec::HasCompact;
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{
	Zero, One, Bounded, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv,
	CheckedShl, CheckedShr, checked_pow, Signed
};
use sp_std::ops::{
	Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign,
	RemAssign, Shl, Shr
};

/// A meta trait for arithmetic type operations, regardless of any limitation on size.
pub trait BaseArithmetic:
	From<u8> +
	Zero + One + IntegerSquareRoot +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedShl + CheckedShr + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv + Saturating +
	PartialOrd<Self> + Ord + Bounded + HasCompact + Sized +
	TryFrom<u8> + TryInto<u8> + TryFrom<u16> + TryInto<u16> + TryFrom<u32> + TryInto<u32> +
	TryFrom<u64> + TryInto<u64> + TryFrom<u128> + TryInto<u128> + TryFrom<usize> + TryInto<usize> +
	UniqueSaturatedFrom<u8> + UniqueSaturatedInto<u8> +
	UniqueSaturatedFrom<u16> + UniqueSaturatedInto<u16> +
	UniqueSaturatedFrom<u32> + UniqueSaturatedInto<u32> +
	UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64> +
	UniqueSaturatedFrom<u128> + UniqueSaturatedInto<u128>
{}

impl<T:
	From<u8> +
	Zero + One + IntegerSquareRoot +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedShl + CheckedShr + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv + Saturating +
	PartialOrd<Self> + Ord + Bounded + HasCompact + Sized +
	TryFrom<u8> + TryInto<u8> + TryFrom<u16> + TryInto<u16> + TryFrom<u32> + TryInto<u32> +
	TryFrom<u64> + TryInto<u64> + TryFrom<u128> + TryInto<u128> + TryFrom<usize> + TryInto<usize> +
	UniqueSaturatedFrom<u8> + UniqueSaturatedInto<u8> +
	UniqueSaturatedFrom<u16> + UniqueSaturatedInto<u16> +
	UniqueSaturatedFrom<u32> + UniqueSaturatedInto<u32> +
	UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64> +
	UniqueSaturatedFrom<u128> + UniqueSaturatedInto<u128>
> BaseArithmetic for T {}

/// A meta trait for arithmetic.
///
/// Arithmetic types do all the usual stuff you'd expect numbers to do. They are guaranteed to
/// be able to represent at least `u32` values without loss, hence the trait implies `From<u32>`
/// and smaller integers. All other conversions are fallible.
pub trait AtLeast32Bit: BaseArithmetic + From<u16> + From<u32> {}

impl<T: BaseArithmetic + From<u16> + From<u32>> AtLeast32Bit for T {}

/// Just like `From` except that if the source value is too big to fit into the destination type
/// then it'll saturate the destination.
pub trait UniqueSaturatedFrom<T: Sized>: Sized {
	/// Convert from a value of `T` into an equivalent instance of `Self`.
	fn unique_saturated_from(t: T) -> Self;
}

/// Just like `Into` except that if the source value is too big to fit into the destination type
/// then it'll saturate the destination.
pub trait UniqueSaturatedInto<T: Sized>: Sized {
	/// Consume self to return an equivalent value of `T`.
	fn unique_saturated_into(self) -> T;
}

impl<T: Sized, S: TryFrom<T> + Bounded + Sized> UniqueSaturatedFrom<T> for S {
	fn unique_saturated_from(t: T) -> Self {
		S::try_from(t).unwrap_or_else(|_| Bounded::max_value())
	}
}

impl<T: Bounded + Sized, S: TryInto<T> + Sized> UniqueSaturatedInto<T> for S {
	fn unique_saturated_into(self) -> T {
		self.try_into().unwrap_or_else(|_| Bounded::max_value())
	}
}

/// Saturating arithmetic operations, returning maximum or minimum values instead of overflowing.
pub trait Saturating {
	/// Saturating addition. Compute `self + rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	fn saturating_add(self, rhs: Self) -> Self;

	/// Saturating subtraction. Compute `self - rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	fn saturating_sub(self, rhs: Self) -> Self;

	/// Saturating multiply. Compute `self * rhs`, saturating at the numeric bounds instead of
	/// overflowing.
	fn saturating_mul(self, rhs: Self) -> Self;

	/// Saturating exponentiation. Compute `self.pow(exp)`, saturating at the numeric bounds
	/// instead of overflowing.
	fn saturating_pow(self, exp: usize) -> Self;
}

impl<T: Clone + One + CheckedMul + Bounded + num_traits::Saturating> Saturating for T {
	fn saturating_add(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_add(self, o)
	}

	fn saturating_sub(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_sub(self, o)
	}

	fn saturating_mul(self, o: Self) -> Self {
		self.checked_mul(&o).unwrap_or_else(Bounded::max_value)
	}

	fn saturating_pow(self, exp: usize) -> Self {
		checked_pow(self, exp).unwrap_or_else(Bounded::max_value)
	}
}

/// Convenience type to work around the highly unergonomic syntax needed
/// to invoke the functions of overloaded generic traits, in this case
/// `SaturatedFrom` and `SaturatedInto`.
pub trait SaturatedConversion {
	/// Convert from a value of `T` into an equivalent instance of `Self`.
	///
	/// This just uses `UniqueSaturatedFrom` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn saturated_from<T>(t: T) -> Self where Self: UniqueSaturatedFrom<T> {
		<Self as UniqueSaturatedFrom<T>>::unique_saturated_from(t)
	}

	/// Consume self to return an equivalent value of `T`.
	///
	/// This just uses `UniqueSaturatedInto` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn saturated_into<T>(self) -> T where Self: UniqueSaturatedInto<T> {
		<Self as UniqueSaturatedInto<T>>::unique_saturated_into(self)
	}
}
impl<T: Sized> SaturatedConversion for T {}

pub trait FixedPointNumber:
	Sized + Copy + Default
	+ Saturating + Bounded
	+ Eq + PartialEq + Ord + PartialOrd
	+ CheckedSub + CheckedAdd + CheckedMul + CheckedDiv
	+ Add + Sub + Div + Mul
	+ Debug
{
	/// The underlying data type used for this fixed point number.
	type Inner: Copy + Debug + One + From<i64>;

	/// The unsigned version of inner.
	type Unsigned;

	/// The previous unsigned.
	type PrevUnsigned;

	/// The perthing used.
	type Perthing;

	/// The accuracy of this fixed point number.
	const BITS: u32;

	/// Accuracy of this `Fixed` implementation.
	fn num_bits() -> u32 {
		Self::BITS
	}

	/// Accuracy of this `Fixed` implementation.
	fn accuracy() -> Self::Inner {
		2i64.pow(Self::BITS).into()
	}

	/// Raw constructor. Equal to `parts / DIV`.
	fn from_inner(inner: Self::Inner) -> Self;

	/// Consume self and return the inner raw value.
	fn into_inner(self) -> Self::Inner;

	/// Creates self from an integer number.
	fn from_integer(int: Self::Inner) -> Self;

	/// Creates self from an integer number.
	fn checked_from_integer(int: Self::Inner) -> Option<Self>;

	/// Creates self from a rational number. Equal to `n / d`.
	///
	/// Assumes d != 0 (returns 0 in this case).
	fn from_rational<N: UniqueSaturatedInto<Self::Inner>>(n: N, d: Self::Inner) -> Self;

	/// Checked multiplication for integer type `N`.
	fn checked_mul_int<
		N: TryFrom<i128> + UniqueSaturatedInto<i128> +
		Copy + Bounded + Saturating +
		Rem<N, Output=N> + Div<N, Output=N> + Mul<N, Output=N> +
		Add<N, Output=N>,
	>(self, other: N) -> Option<N>;

	/// Checked division for integer type `N`.
	fn checked_div_int<N: Copy + TryFrom<i128> + UniqueSaturatedInto<i128>>(self, other: N) -> Option<N>;

	/// Saturating multiplication for integer type `N`.
	fn saturating_mul_int<
		N: TryFrom<i128> + UniqueSaturatedInto<i128> +
		Copy + Bounded + Saturating +
		Rem<N, Output=N> + Div<N, Output=N> + Mul<N, Output=N> +
		Add<N, Output=N>,
	>(self, other: N) -> N;

	/// Performs a saturated multiplication and accumulate by unsigned number.
	///
	/// Returns a saturated `int + (self * int)`.
	fn saturated_multiply_accumulate<
		N: TryFrom<i128> + UniqueSaturatedInto<i128> +
			Copy + Bounded + Saturating +
			Rem<N, Output=N> + Div<N, Output=N> + Mul<N, Output=N> +
			Add<N, Output=N>,
	>(self, int: N) -> N;

	/// Saturating absolute value. Returning MAX if `parts == Inner::MIN` instead of overflowing.
	fn saturating_abs(self) -> Self;

	/// Returns zero.
	fn zero() -> Self;

	/// Checks if the number is zero.
	fn is_zero(&self) -> bool;

	/// Returns one.
	fn one() -> Self;

	/// Checks if the number is positive.
	fn is_positive(self) -> bool;

	/// Checks if the number is negative.
	fn is_negative(self) -> bool;

	/// Takes the reciprocal (inverse), `1 / self`.
	fn reciprocal(self) -> Option<Self> {
		Self::one().checked_div(&self)
	}
}
