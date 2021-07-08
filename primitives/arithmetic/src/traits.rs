// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use sp_std::{self, convert::{TryFrom, TryInto}};
use codec::HasCompact;
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{
	Zero, One, Bounded, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, CheckedNeg,
	CheckedShl, CheckedShr, checked_pow, Signed, Unsigned,
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
	fn saturating_inc(&mut self) where Self: One {
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_add(One::one());
	}

	/// Decrement self by one, saturating at zero.
	fn saturating_dec(&mut self) where Self: One {
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_sub(One::one());
	}

	/// Increment self by some `amount`, saturating.
	fn saturating_accrue(&mut self, amount: Self) where Self: One {
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_add(amount);
	}

	/// Decrement self by some `amount`, saturating at zero.
	fn saturating_reduce(&mut self, amount: Self) where Self: One {
		let mut o = Self::one();
		sp_std::mem::swap(&mut o, self);
		*self = o.saturating_sub(amount);
	}
}

impl<T: Clone + Zero + One + PartialOrd + CheckedMul + Bounded + num_traits::Saturating> Saturating for T {
	fn saturating_add(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_add(self, o)
	}

	fn saturating_sub(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_sub(self, o)
	}

	fn saturating_mul(self, o: Self) -> Self {
		self.checked_mul(&o)
			.unwrap_or_else(||
				if (self < T::zero()) != (o < T::zero()) {
					Bounded::min_value()
				} else {
					Bounded::max_value()
				}
			)
	}

	fn saturating_pow(self, exp: usize) -> Self {
		let neg = self < T::zero() && exp % 2 != 0;
		checked_pow(self, exp)
			.unwrap_or_else(||
				if neg {
					Bounded::min_value()
				} else {
					Bounded::max_value()
				}
			)
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
