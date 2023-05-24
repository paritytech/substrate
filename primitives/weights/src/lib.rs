// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Primitives for transaction weighting.

#![cfg_attr(not(feature = "std"), no_std)]
// TODO remove once `OldWeight` is gone. I dont know why this is needed, maybe by one of the macros
// of `OldWeight`.
#![allow(deprecated)]

extern crate self as sp_weights;

mod weight_meter;
mod weight_v2;

use codec::{CompactAs, Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use sp_arithmetic::{
	traits::{BaseArithmetic, SaturatedConversion, Unsigned},
	Perbill,
};
use sp_core::Get;
use sp_debug_derive::RuntimeDebug;

pub use weight_meter::*;
pub use weight_v2::*;

pub mod constants {
	pub const WEIGHT_REF_TIME_PER_SECOND: u64 = 1_000_000_000_000;
	pub const WEIGHT_REF_TIME_PER_MILLIS: u64 = 1_000_000_000;
	pub const WEIGHT_REF_TIME_PER_MICROS: u64 = 1_000_000;
	pub const WEIGHT_REF_TIME_PER_NANOS: u64 = 1_000;

	pub const WEIGHT_PROOF_SIZE_PER_MB: u64 = 1024 * 1024;
	pub const WEIGHT_PROOF_SIZE_PER_KB: u64 = 1024;
}

/// The old weight type.
///
/// NOTE: This type exists purely for compatibility purposes! Use [`weight_v2::Weight`] in all other
/// cases.
#[derive(
	Decode,
	Encode,
	CompactAs,
	PartialEq,
	Eq,
	Clone,
	Copy,
	RuntimeDebug,
	Default,
	MaxEncodedLen,
	TypeInfo,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[deprecated(note = "Will be removed soon; use `Weight` instead.")]
pub struct OldWeight(pub u64);

/// The weight of database operations that the runtime can invoke.
///
/// NOTE: This is currently only measured in computational time, and will probably
/// be updated all together once proof size is accounted for.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo)]
pub struct RuntimeDbWeight {
	pub read: u64,
	pub write: u64,
}

impl RuntimeDbWeight {
	pub fn reads(self, r: u64) -> Weight {
		Weight::from_parts(self.read.saturating_mul(r), 0)
	}

	pub fn writes(self, w: u64) -> Weight {
		Weight::from_parts(self.write.saturating_mul(w), 0)
	}

	pub fn reads_writes(self, r: u64, w: u64) -> Weight {
		let read_weight = self.read.saturating_mul(r);
		let write_weight = self.write.saturating_mul(w);
		Weight::from_parts(read_weight.saturating_add(write_weight), 0)
	}
}

/// One coefficient and its position in the `WeightToFee`.
///
/// One term of polynomial is calculated as:
///
/// ```ignore
/// coeff_integer * x^(degree) + coeff_frac * x^(degree)
/// ```
///
/// The `negative` value encodes whether the term is added or subtracted from the
/// overall polynomial result.
#[derive(Clone, Encode, Decode, TypeInfo)]
pub struct WeightToFeeCoefficient<Balance> {
	/// The integral part of the coefficient.
	pub coeff_integer: Balance,
	/// The fractional part of the coefficient.
	pub coeff_frac: Perbill,
	/// True iff the coefficient should be interpreted as negative.
	pub negative: bool,
	/// Degree/exponent of the term.
	pub degree: u8,
}

impl<Balance> WeightToFeeCoefficient<Balance>
where
	Balance: BaseArithmetic + From<u32> + Copy + Unsigned,
{
	/// Evaluate the term at `x` and saturatingly amalgamate into `result`.
	///
	/// The unsigned value for the term is calculated as:
	/// ```ignore
	/// (frac * x^(degree) + integer * x^(degree))
	/// ```
	/// Depending on the value of `negative`, it is added or subtracted from the `result`.
	pub fn saturating_eval(&self, mut result: Balance, x: Balance) -> Balance {
		let power = x.saturating_pow(self.degree.into());

		let frac = self.coeff_frac * power; // Overflow safe.
		let integer = self.coeff_integer.saturating_mul(power);
		// Do not add them together here to avoid an underflow.

		if self.negative {
			result = result.saturating_sub(frac);
			result = result.saturating_sub(integer);
		} else {
			result = result.saturating_add(frac);
			result = result.saturating_add(integer);
		}

		result
	}
}

/// A list of coefficients that represent a polynomial.
pub type WeightToFeeCoefficients<T> = SmallVec<[WeightToFeeCoefficient<T>; 4]>;

/// A list of coefficients that represent a polynomial.
///
/// Can be [eval](Self::eval)uated at a specific `u64` to get the fee. The evaluations happens by
/// summing up all term [results](`WeightToFeeCoefficient::saturating_eval`). The order of the
/// coefficients matters since it uses saturating arithmetic. This struct does therefore not model a
/// polynomial in the mathematical sense (polynomial ring).
///
/// For visualization purposes, the formulas of the unsigned terms look like:
///
/// ```ignore
/// (c[0].frac * x^(c[0].degree) + c[0].integer * x^(c[0].degree))
/// (c[1].frac * x^(c[1].degree) + c[1].integer * x^(c[1].degree))
/// ...
/// ```
/// Depending on the value of `c[i].negative`, each term is added or subtracted from the result.
/// The result is initialized as zero.
pub struct FeePolynomial<Balance> {
	coefficients: SmallVec<[WeightToFeeCoefficient<Balance>; 4]>,
}

impl<Balance> From<WeightToFeeCoefficients<Balance>> for FeePolynomial<Balance> {
	fn from(coefficients: WeightToFeeCoefficients<Balance>) -> Self {
		Self { coefficients }
	}
}

impl<Balance> FeePolynomial<Balance>
where
	Balance: BaseArithmetic + From<u32> + Copy + Unsigned,
{
	/// Evaluate the polynomial at a specific `x`.
	pub fn eval(&self, x: u64) -> Balance {
		self.coefficients.iter().fold(Balance::zero(), |acc, term| {
			term.saturating_eval(acc, Balance::saturated_from(x))
		})
	}
}

/// A trait that describes the weight to fee calculation.
pub trait WeightToFee {
	/// The type that is returned as result from calculation.
	type Balance: BaseArithmetic + From<u32> + Copy + Unsigned;

	/// Calculates the fee from the passed `weight`.
	fn weight_to_fee(weight: &Weight) -> Self::Balance;
}

/// A trait that describes the weight to fee calculation as polynomial.
///
/// An implementor should only implement the `polynomial` function.
pub trait WeightToFeePolynomial {
	/// The type that is returned as result from polynomial evaluation.
	type Balance: BaseArithmetic + From<u32> + Copy + Unsigned;

	/// Returns a polynomial that describes the weight to fee conversion.
	///
	/// This is the only function that should be manually implemented. Please note
	/// that all calculation is done in the probably unsigned `Balance` type. This means
	/// that the order of coefficients is important as putting the negative coefficients
	/// first will most likely saturate the result to zero mid evaluation.
	fn polynomial() -> WeightToFeeCoefficients<Self::Balance>;
}

impl<T> WeightToFee for T
where
	T: WeightToFeePolynomial,
{
	type Balance = <Self as WeightToFeePolynomial>::Balance;

	/// Calculates the fee from the passed `weight` according to the `polynomial`.
	///
	/// This should not be overridden in most circumstances. Calculation is done in the
	/// `Balance` type and never overflows. All evaluation is saturating.
	fn weight_to_fee(weight: &Weight) -> Self::Balance {
		let poly: FeePolynomial<Self::Balance> = Self::polynomial().into();
		poly.eval(weight.ref_time())
	}
}

/// Implementor of `WeightToFee` that maps one unit of weight to one unit of fee.
pub struct IdentityFee<T>(sp_std::marker::PhantomData<T>);

impl<T> WeightToFee for IdentityFee<T>
where
	T: BaseArithmetic + From<u32> + Copy + Unsigned,
{
	type Balance = T;

	fn weight_to_fee(weight: &Weight) -> Self::Balance {
		Self::Balance::saturated_from(weight.ref_time())
	}
}

/// Implementor of [`WeightToFee`] that uses a constant multiplier.
/// # Example
///
/// ```
/// # use sp_core::ConstU128;
/// # use sp_weights::ConstantMultiplier;
/// // Results in a multiplier of 10 for each unit of weight (or length)
/// type LengthToFee = ConstantMultiplier::<u128, ConstU128<10u128>>;
/// ```
pub struct ConstantMultiplier<T, M>(sp_std::marker::PhantomData<(T, M)>);

impl<T, M> WeightToFee for ConstantMultiplier<T, M>
where
	T: BaseArithmetic + From<u32> + Copy + Unsigned,
	M: Get<T>,
{
	type Balance = T;

	fn weight_to_fee(weight: &Weight) -> Self::Balance {
		Self::Balance::saturated_from(weight.ref_time()).saturating_mul(M::get())
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use super::*;
	use smallvec::smallvec;

	type Balance = u64;

	// 0.5x^3 + 2.333x^2 + 7x - 10_000
	struct Poly;
	impl WeightToFeePolynomial for Poly {
		type Balance = Balance;

		fn polynomial() -> WeightToFeeCoefficients<Self::Balance> {
			smallvec![
				WeightToFeeCoefficient {
					coeff_integer: 0,
					coeff_frac: Perbill::from_float(0.5),
					negative: false,
					degree: 3
				},
				WeightToFeeCoefficient {
					coeff_integer: 2,
					coeff_frac: Perbill::from_rational(1u32, 3u32),
					negative: false,
					degree: 2
				},
				WeightToFeeCoefficient {
					coeff_integer: 7,
					coeff_frac: Perbill::zero(),
					negative: false,
					degree: 1
				},
				WeightToFeeCoefficient {
					coeff_integer: 10_000,
					coeff_frac: Perbill::zero(),
					negative: true,
					degree: 0
				},
			]
		}
	}

	#[test]
	fn polynomial_works() {
		// 100^3/2=500000 100^2*(2+1/3)=23333 700 -10000
		assert_eq!(Poly::weight_to_fee(&Weight::from_parts(100, 0)), 514033);
		// 10123^3/2=518677865433 10123^2*(2+1/3)=239108634 70861 -10000
		assert_eq!(Poly::weight_to_fee(&Weight::from_parts(10_123, 0)), 518917034928);
	}

	#[test]
	fn polynomial_does_not_underflow() {
		assert_eq!(Poly::weight_to_fee(&Weight::zero()), 0);
		assert_eq!(Poly::weight_to_fee(&Weight::from_parts(10, 0)), 0);
	}

	#[test]
	fn polynomial_does_not_overflow() {
		assert_eq!(Poly::weight_to_fee(&Weight::MAX), Balance::max_value() - 10_000);
	}

	#[test]
	fn identity_fee_works() {
		assert_eq!(IdentityFee::<Balance>::weight_to_fee(&Weight::zero()), 0);
		assert_eq!(IdentityFee::<Balance>::weight_to_fee(&Weight::from_parts(50, 0)), 50);
		assert_eq!(IdentityFee::<Balance>::weight_to_fee(&Weight::MAX), Balance::max_value());
	}

	#[test]
	fn constant_fee_works() {
		use sp_core::ConstU128;
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<100u128>>::weight_to_fee(&Weight::zero()),
			0
		);
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<10u128>>::weight_to_fee(&Weight::from_parts(
				50, 0
			)),
			500
		);
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<1024u128>>::weight_to_fee(&Weight::from_parts(
				16, 0
			)),
			16384
		);
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<{ u128::MAX }>>::weight_to_fee(
				&Weight::from_parts(2, 0)
			),
			u128::MAX
		);
	}
}
