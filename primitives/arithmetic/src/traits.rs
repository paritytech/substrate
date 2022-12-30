// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Primitive traits for the runtime arithmetic.

use codec::HasCompact;
pub use ensure::{
	Ensure, EnsureAdd, EnsureAddAssign, EnsureDiv, EnsureDivAssign, EnsureFixedPointNumber,
	EnsureFrom, EnsureInto, EnsureMul, EnsureMulAssign, EnsureOp, EnsureOpAssign, EnsureSub,
	EnsureSubAssign,
};
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{
	checked_pow, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl,
	CheckedShr, CheckedSub, One, Signed, Unsigned, Zero,
};
use sp_std::ops::{
	Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Shl, Shr, Sub, SubAssign,
};

/// A meta trait for arithmetic type operations, regardless of any limitation on size.
pub trait BaseArithmetic:
	From<u8>
	+ Zero
	+ One
	+ IntegerSquareRoot
	+ Add<Self, Output = Self>
	+ AddAssign<Self>
	+ Sub<Self, Output = Self>
	+ SubAssign<Self>
	+ Mul<Self, Output = Self>
	+ MulAssign<Self>
	+ Div<Self, Output = Self>
	+ DivAssign<Self>
	+ Rem<Self, Output = Self>
	+ RemAssign<Self>
	+ Shl<u32, Output = Self>
	+ Shr<u32, Output = Self>
	+ CheckedShl
	+ CheckedShr
	+ CheckedAdd
	+ CheckedSub
	+ CheckedMul
	+ CheckedDiv
	+ CheckedRem
	+ Saturating
	+ PartialOrd<Self>
	+ Ord
	+ Bounded
	+ HasCompact
	+ Sized
	+ Clone
	+ TryFrom<u8>
	+ TryInto<u8>
	+ TryFrom<u16>
	+ TryInto<u16>
	+ TryFrom<u32>
	+ TryInto<u32>
	+ TryFrom<u64>
	+ TryInto<u64>
	+ TryFrom<u128>
	+ TryInto<u128>
	+ TryFrom<usize>
	+ TryInto<usize>
	+ UniqueSaturatedFrom<u8>
	+ UniqueSaturatedInto<u8>
	+ UniqueSaturatedFrom<u16>
	+ UniqueSaturatedInto<u16>
	+ UniqueSaturatedFrom<u32>
	+ UniqueSaturatedInto<u32>
	+ UniqueSaturatedFrom<u64>
	+ UniqueSaturatedInto<u64>
	+ UniqueSaturatedFrom<u128>
	+ UniqueSaturatedInto<u128>
{
}

impl<
		T: From<u8>
			+ Zero
			+ One
			+ IntegerSquareRoot
			+ Add<Self, Output = Self>
			+ AddAssign<Self>
			+ Sub<Self, Output = Self>
			+ SubAssign<Self>
			+ Mul<Self, Output = Self>
			+ MulAssign<Self>
			+ Div<Self, Output = Self>
			+ DivAssign<Self>
			+ Rem<Self, Output = Self>
			+ RemAssign<Self>
			+ Shl<u32, Output = Self>
			+ Shr<u32, Output = Self>
			+ CheckedShl
			+ CheckedShr
			+ CheckedAdd
			+ CheckedSub
			+ CheckedMul
			+ CheckedDiv
			+ CheckedRem
			+ Saturating
			+ PartialOrd<Self>
			+ Ord
			+ Bounded
			+ HasCompact
			+ Sized
			+ Clone
			+ TryFrom<u8>
			+ TryInto<u8>
			+ TryFrom<u16>
			+ TryInto<u16>
			+ TryFrom<u32>
			+ TryInto<u32>
			+ TryFrom<u64>
			+ TryInto<u64>
			+ TryFrom<u128>
			+ TryInto<u128>
			+ TryFrom<usize>
			+ TryInto<usize>
			+ UniqueSaturatedFrom<u8>
			+ UniqueSaturatedInto<u8>
			+ UniqueSaturatedFrom<u16>
			+ UniqueSaturatedInto<u16>
			+ UniqueSaturatedFrom<u32>
			+ UniqueSaturatedInto<u32>
			+ UniqueSaturatedFrom<u64>
			+ UniqueSaturatedInto<u64>
			+ UniqueSaturatedFrom<u128>
			+ UniqueSaturatedInto<u128>,
	> BaseArithmetic for T
{
}

/// A meta trait for arithmetic.
///
/// Arithmetic types do all the usual stuff you'd expect numbers to do. They are guaranteed to
/// be able to represent at least `u32` values without loss, hence the trait implies `From<u32>`
/// and smaller integers. All other conversions are fallible.
pub trait AtLeast32Bit: BaseArithmetic + From<u16> + From<u32> {}

impl<T: BaseArithmetic + From<u16> + From<u32>> AtLeast32Bit for T {}

/// A meta trait for arithmetic.  Same as [`AtLeast32Bit `], but also bounded to be unsigned.
pub trait AtLeast32BitUnsigned: AtLeast32Bit + Unsigned {}

impl<T: AtLeast32Bit + Unsigned> AtLeast32BitUnsigned for T {}

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

	/// Increment self by one, saturating.
	fn saturating_inc(&mut self)
	where
		Self: One,
	{
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_add(One::one());
	}

	/// Decrement self by one, saturating at zero.
	fn saturating_dec(&mut self)
	where
		Self: One,
	{
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_sub(One::one());
	}

	/// Increment self by some `amount`, saturating.
	fn saturating_accrue(&mut self, amount: Self)
	where
		Self: One,
	{
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_add(amount);
	}

	/// Decrement self by some `amount`, saturating at zero.
	fn saturating_reduce(&mut self, amount: Self)
	where
		Self: One,
	{
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_sub(amount);
	}
}

impl<T: Clone + Zero + One + PartialOrd + CheckedMul + Bounded + num_traits::Saturating> Saturating
	for T
{
	fn saturating_add(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_add(self, o)
	}

	fn saturating_sub(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_sub(self, o)
	}

	fn saturating_mul(self, o: Self) -> Self {
		self.checked_mul(&o).unwrap_or_else(|| {
			if (self < T::zero()) != (o < T::zero()) {
				Bounded::min_value()
			} else {
				Bounded::max_value()
			}
		})
	}

	fn saturating_pow(self, exp: usize) -> Self {
		let neg = self < T::zero() && exp % 2 != 0;
		checked_pow(self, exp).unwrap_or_else(|| {
			if neg {
				Bounded::min_value()
			} else {
				Bounded::max_value()
			}
		})
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
	fn saturated_from<T>(t: T) -> Self
	where
		Self: UniqueSaturatedFrom<T>,
	{
		<Self as UniqueSaturatedFrom<T>>::unique_saturated_from(t)
	}

	/// Consume self to return an equivalent value of `T`.
	///
	/// This just uses `UniqueSaturatedInto` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn saturated_into<T>(self) -> T
	where
		Self: UniqueSaturatedInto<T>,
	{
		<Self as UniqueSaturatedInto<T>>::unique_saturated_into(self)
	}
}
impl<T: Sized> SaturatedConversion for T {}

/// Arithmetic operations with safe error handling.
///
/// This module provide a readable way to do safe arithmetics, turning this:
///
/// ```
/// # use sp_arithmetic::{traits::EnsureSub, ArithmeticError};
/// # fn foo() -> Result<(), ArithmeticError> {
/// # let mut my_value: i32 = 1;
/// # let other_value: i32 = 1;
/// my_value = my_value.checked_sub(other_value).ok_or(ArithmeticError::Overflow)?;
/// # Ok(())
/// # }
/// ```
///
/// into this:
///
/// ```
/// # use sp_arithmetic::{traits::EnsureSubAssign, ArithmeticError};
/// # fn foo() -> Result<(), ArithmeticError> {
/// # let mut my_value: i32 = 1;
/// # let other_value: i32 = 1;
/// my_value.ensure_sub_assign(other_value)?;
/// # Ok(())
/// # }
/// ```
///
/// choosing the correct [`ArithmeticError`](crate::ArithmeticError) it should return in case of
/// fail.
///
/// The *EnsureOps* family functions follows the same behavior as *CheckedOps* but
/// returning an [`ArithmeticError`](crate::ArithmeticError) instead of `None`.
mod ensure {
	use super::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Zero};
	use crate::{ArithmeticError, FixedPointNumber, FixedPointOperand};

	/// Performs addition that returns [`ArithmeticError`] instead of wrapping around on overflow.
	pub trait EnsureAdd: CheckedAdd + PartialOrd + Zero + Copy {
		/// Adds two numbers, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// Similar to [`CheckedAdd::checked_add()`] but returning an [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureAdd, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     u32::MAX.ensure_add(1)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     i32::MIN.ensure_add(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_add(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_add(&v).ok_or_else(|| error::equivalent(v))
		}
	}

	/// Performs subtraction that returns [`ArithmeticError`] instead of wrapping around on
	/// underflow.
	pub trait EnsureSub: CheckedSub + PartialOrd + Zero + Copy {
		/// Subtracts two numbers, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// Similar to [`CheckedSub::checked_sub()`] but returning an [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureSub, ArithmeticError};
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     0u32.ensure_sub(1)?;
		///     Ok(())
		/// }
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     i32::MAX.ensure_sub(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// ```
		fn ensure_sub(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_sub(&v).ok_or_else(|| error::inverse(v))
		}
	}

	/// Performs multiplication that returns [`ArithmeticError`] instead of wrapping around on
	/// overflow.
	pub trait EnsureMul: CheckedMul + PartialOrd + Zero + Copy {
		/// Multiplies two numbers, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// Similar to [`CheckedMul::checked_mul()`] but returning an [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureMul, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     u32::MAX.ensure_mul(2)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     i32::MAX.ensure_mul(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_mul(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_mul(&v).ok_or_else(|| error::multiplication(self, v))
		}
	}

	/// Performs division that returns [`ArithmeticError`] instead of wrapping around on overflow.
	pub trait EnsureDiv: CheckedDiv + PartialOrd + Zero + Copy {
		/// Divides two numbers, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// Similar to [`CheckedDiv::checked_div()`] but returning an [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureDiv, ArithmeticError};
		///
		/// fn extrinsic_zero() -> Result<(), ArithmeticError> {
		///     1.ensure_div(0)?;
		///     Ok(())
		/// }
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     i64::MIN.ensure_div(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero));
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// ```
		fn ensure_div(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_div(&v).ok_or_else(|| error::division(self, v))
		}
	}

	impl<T: CheckedAdd + PartialOrd + Zero + Copy> EnsureAdd for T {}
	impl<T: CheckedSub + PartialOrd + Zero + Copy> EnsureSub for T {}
	impl<T: CheckedMul + PartialOrd + Zero + Copy> EnsureMul for T {}
	impl<T: CheckedDiv + PartialOrd + Zero + Copy> EnsureDiv for T {}

	/// Meta trait that supports all immutable arithmetic `Ensure*` operations
	pub trait EnsureOp: EnsureAdd + EnsureSub + EnsureMul + EnsureDiv {}
	impl<T: EnsureAdd + EnsureSub + EnsureMul + EnsureDiv> EnsureOp for T {}

	/// Performs self addition that returns [`ArithmeticError`] instead of wrapping around on
	/// overflow.
	pub trait EnsureAddAssign: EnsureAdd {
		/// Adds two numbers overwriting the left hand one, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureAddAssign, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let mut max = u32::MAX;
		///     max.ensure_add_assign(1)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     let mut max = i32::MIN;
		///     max.ensure_add_assign(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_add_assign(&mut self, v: Self) -> Result<(), ArithmeticError> {
			*self = self.ensure_add(v)?;
			Ok(())
		}
	}

	/// Performs self subtraction that returns [`ArithmeticError`] instead of wrapping around on
	/// underflow.
	pub trait EnsureSubAssign: EnsureSub {
		/// Subtracts two numbers overwriting the left hand one, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureSubAssign, ArithmeticError};
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     let mut zero: u32 = 0;
		///     zero.ensure_sub_assign(1)?;
		///     Ok(())
		/// }
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let mut zero = i32::MAX;
		///     zero.ensure_sub_assign(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// ```
		fn ensure_sub_assign(&mut self, v: Self) -> Result<(), ArithmeticError> {
			*self = self.ensure_sub(v)?;
			Ok(())
		}
	}

	/// Performs self multiplication that returns [`ArithmeticError`] instead of wrapping around on
	/// overflow.
	pub trait EnsureMulAssign: EnsureMul {
		/// Multiplies two numbers overwriting the left hand one, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureMulAssign, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let mut max = u32::MAX;
		///     max.ensure_mul_assign(2)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     let mut max = i32::MAX;
		///     max.ensure_mul_assign(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_mul_assign(&mut self, v: Self) -> Result<(), ArithmeticError> {
			*self = self.ensure_mul(v)?;
			Ok(())
		}
	}

	/// Performs self division that returns [`ArithmeticError`] instead of wrapping around on
	/// overflow.
	pub trait EnsureDivAssign: EnsureDiv {
		/// Divides two numbers overwriting the left hand one, checking for overflow.
		///
		/// If it fails, [`ArithmeticError`] is returned.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureDivAssign, ArithmeticError, FixedI64};
		///
		/// fn extrinsic_zero() -> Result<(), ArithmeticError> {
		///     let mut one = 1;
		///     one.ensure_div_assign(0)?;
		///     Ok(())
		/// }
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let mut min = FixedI64::from(i64::MIN);
		///     min.ensure_div_assign(FixedI64::from(-1))?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero));
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// ```
		fn ensure_div_assign(&mut self, v: Self) -> Result<(), ArithmeticError> {
			*self = self.ensure_div(v)?;
			Ok(())
		}
	}

	impl<T: EnsureAdd> EnsureAddAssign for T {}
	impl<T: EnsureSub> EnsureSubAssign for T {}
	impl<T: EnsureMul> EnsureMulAssign for T {}
	impl<T: EnsureDiv> EnsureDivAssign for T {}

	/// Meta trait that supports all assigned arithmetic `Ensure*` operations
	pub trait EnsureOpAssign:
		EnsureAddAssign + EnsureSubAssign + EnsureMulAssign + EnsureDivAssign
	{
	}
	impl<T: EnsureAddAssign + EnsureSubAssign + EnsureMulAssign + EnsureDivAssign> EnsureOpAssign
		for T
	{
	}

	/// Meta trait that supports all arithmetic operations
	pub trait Ensure: EnsureOp + EnsureOpAssign {}
	impl<T: EnsureOp + EnsureOpAssign> Ensure for T {}

	/// Extends [`FixedPointNumber`] with the Ensure family functions.
	pub trait EnsureFixedPointNumber: FixedPointNumber {
		/// Creates `self` from a rational number. Equal to `n / d`.
		///
		/// Returns [`ArithmeticError`] if `d == 0` or `n / d` exceeds accuracy.
		///
		/// Similar to [`FixedPointNumber::checked_from_rational()`] but returning an
		/// [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureFixedPointNumber, ArithmeticError, FixedI64};
		///
		/// fn extrinsic_zero() -> Result<(), ArithmeticError> {
		///     FixedI64::ensure_from_rational(1, 0)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     FixedI64::ensure_from_rational(i64::MAX, -1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_from_rational<N: FixedPointOperand, D: FixedPointOperand>(
			n: N,
			d: D,
		) -> Result<Self, ArithmeticError> {
			<Self as FixedPointNumber>::checked_from_rational(n, d)
				.ok_or_else(|| error::division(n, d))
		}

		/// Ensure multiplication for integer type `N`. Equal to `self * n`.
		///
		/// Returns [`ArithmeticError`] if the result does not fit in `N`.
		///
		/// Similar to [`FixedPointNumber::checked_mul_int()`] but returning an [`ArithmeticError`]
		/// error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureFixedPointNumber, ArithmeticError, FixedI64};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     FixedI64::from(i64::MAX).ensure_mul_int(2)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     FixedI64::from(i64::MAX).ensure_mul_int(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_mul_int<N: FixedPointOperand>(self, n: N) -> Result<N, ArithmeticError> {
			self.checked_mul_int(n).ok_or_else(|| error::multiplication(self, n))
		}

		/// Ensure division for integer type `N`. Equal to `self / d`.
		///
		/// Returns [`ArithmeticError`] if the result does not fit in `N` or `d == 0`.
		///
		/// Similar to [`FixedPointNumber::checked_div_int()`] but returning an [`ArithmeticError`]
		/// error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureFixedPointNumber, ArithmeticError, FixedI64};
		///
		/// fn extrinsic_zero() -> Result<(), ArithmeticError> {
		///     FixedI64::from(1).ensure_div_int(0)?;
		///     Ok(())
		/// }
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     FixedI64::from(i64::MIN).ensure_div_int(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero));
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// ```
		fn ensure_div_int<D: FixedPointOperand>(self, d: D) -> Result<D, ArithmeticError> {
			self.checked_div_int(d).ok_or_else(|| error::division(self, d))
		}
	}

	impl<T: FixedPointNumber> EnsureFixedPointNumber for T {}

	/// Similar to [`TryFrom`] but returning an [`ArithmeticError`] error.
	pub trait EnsureFrom<T: PartialOrd + Zero + Copy>:
		TryFrom<T> + PartialOrd + Zero + Copy
	{
		/// Performs the conversion returning an [`ArithmeticError`] if fails.
		///
		/// Similar to [`TryFrom::try_from()`] but returning an [`ArithmeticError`] error.
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureFrom, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let byte: u8 = u8::ensure_from(256u16)?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     let byte: i8 = i8::ensure_from(-129i16)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_from(other: T) -> Result<Self, ArithmeticError> {
			Self::try_from(other).map_err(|_| error::equivalent(other))
		}
	}

	/// Similar to [`TryInto`] but returning an [`ArithmeticError`] error.
	pub trait EnsureInto<T: PartialOrd + Zero + Copy>:
		TryInto<T> + PartialOrd + Zero + Copy
	{
		/// Performs the conversion returning an [`ArithmeticError`] if fails.
		///
		/// Similar to [`TryInto::try_into()`] but returning an [`ArithmeticError`] error
		///
		/// ```
		/// use sp_arithmetic::{traits::EnsureInto, ArithmeticError};
		///
		/// fn overflow() -> Result<(), ArithmeticError> {
		///     let byte: u8 = 256u16.ensure_into()?;
		///     Ok(())
		/// }
		///
		/// fn underflow() -> Result<(), ArithmeticError> {
		///     let byte: i8 = (-129i16).ensure_into()?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(overflow(), Err(ArithmeticError::Overflow));
		/// assert_eq!(underflow(), Err(ArithmeticError::Underflow));
		/// ```
		fn ensure_into(self) -> Result<T, ArithmeticError> {
			self.try_into().map_err(|_| error::equivalent(self))
		}
	}

	impl<T: TryFrom<S> + PartialOrd + Zero + Copy, S: PartialOrd + Zero + Copy> EnsureFrom<S> for T {}
	impl<T: TryInto<S> + PartialOrd + Zero + Copy, S: PartialOrd + Zero + Copy> EnsureInto<S> for T {}

	mod error {
		use super::{ArithmeticError, Zero};

		#[derive(PartialEq)]
		enum Signum {
			Negative,
			Positive,
		}

		impl<T: PartialOrd + Zero> From<T> for Signum {
			fn from(value: T) -> Self {
				if value < Zero::zero() {
					Signum::Negative
				} else {
					Signum::Positive
				}
			}
		}

		impl sp_std::ops::Mul for Signum {
			type Output = Self;

			fn mul(self, rhs: Self) -> Self {
				if self != rhs {
					Signum::Negative
				} else {
					Signum::Positive
				}
			}
		}

		pub fn equivalent<R: PartialOrd + Zero + Copy>(r: R) -> ArithmeticError {
			match Signum::from(r) {
				Signum::Negative => ArithmeticError::Underflow,
				Signum::Positive => ArithmeticError::Overflow,
			}
		}

		pub fn inverse<R: PartialOrd + Zero + Copy>(r: R) -> ArithmeticError {
			match Signum::from(r) {
				Signum::Negative => ArithmeticError::Overflow,
				Signum::Positive => ArithmeticError::Underflow,
			}
		}

		pub fn multiplication<L: PartialOrd + Zero + Copy, R: PartialOrd + Zero + Copy>(
			l: L,
			r: R,
		) -> ArithmeticError {
			match Signum::from(l) * Signum::from(r) {
				Signum::Negative => ArithmeticError::Underflow,
				Signum::Positive => ArithmeticError::Overflow,
			}
		}

		pub fn division<N: PartialOrd + Zero + Copy, D: PartialOrd + Zero + Copy>(
			n: N,
			d: D,
		) -> ArithmeticError {
			if d.is_zero() {
				ArithmeticError::DivisionByZero
			} else {
				multiplication(n, d)
			}
		}
	}
}
