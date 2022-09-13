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

//! # Primitives for transaction weighting.
//!
//! Latest machine specification used to benchmark are:
//! - Digital Ocean: ubuntu-s-2vcpu-4gb-ams3-01
//! - 2x Intel(R) Xeon(R) CPU E5-2650 v4 @ 2.20GHz
//! - 4GB RAM
//! - Ubuntu 19.10 (GNU/Linux 5.3.0-18-generic x86_64)
//! - rustc 1.42.0 (b8cedc004 2020-03-09)

#![cfg_attr(not(feature = "std"), no_std)]

extern crate self as sp_weights;

mod weight_v2;

use codec::{Decode, Encode};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use sp_arithmetic::{
	traits::{BaseArithmetic, SaturatedConversion, Saturating, Unsigned},
	Perbill,
};
use sp_core::Get;
use sp_debug_derive::RuntimeDebug;

pub use weight_v2::*;

pub mod constants {
	use super::Weight;

	pub const WEIGHT_PER_SECOND: Weight = Weight::from_ref_time(1_000_000_000_000);
	pub const WEIGHT_PER_MILLIS: Weight = Weight::from_ref_time(1_000_000_000);
	pub const WEIGHT_PER_MICROS: Weight = Weight::from_ref_time(1_000_000);
	pub const WEIGHT_PER_NANOS: Weight = Weight::from_ref_time(1_000);
}

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
		Weight::from_ref_time(self.read.saturating_mul(r))
	}

	pub fn writes(self, w: u64) -> Weight {
		Weight::from_ref_time(self.write.saturating_mul(w))
	}

	pub fn reads_writes(self, r: u64, w: u64) -> Weight {
		let read_weight = self.read.saturating_mul(r);
		let write_weight = self.write.saturating_mul(w);
		Weight::from_ref_time(read_weight.saturating_add(write_weight))
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
/// The `negative` value encodes whether the term is added or substracted from the
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

/// A list of coefficients that represent one polynomial.
pub type WeightToFeeCoefficients<T> = SmallVec<[WeightToFeeCoefficient<T>; 4]>;

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
		Self::polynomial()
			.iter()
			.fold(Self::Balance::saturated_from(0u32), |mut acc, args| {
				let w = Self::Balance::saturated_from(weight.ref_time())
					.saturating_pow(args.degree.into());

				// The sum could get negative. Therefore we only sum with the accumulator.
				// The Perbill Mul implementation is non overflowing.
				let frac = args.coeff_frac * w;
				let integer = args.coeff_integer.saturating_mul(w);

				if args.negative {
					acc = acc.saturating_sub(frac);
					acc = acc.saturating_sub(integer);
				} else {
					acc = acc.saturating_add(frac);
					acc = acc.saturating_add(integer);
				}

				acc
			})
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
		assert_eq!(Poly::weight_to_fee(&Weight::from_ref_time(100)), 514033);
		// 10123^3/2=518677865433 10123^2*(2+1/3)=239108634 70861 -10000
		assert_eq!(Poly::weight_to_fee(&Weight::from_ref_time(10_123)), 518917034928);
	}

	#[test]
	fn polynomial_does_not_underflow() {
		assert_eq!(Poly::weight_to_fee(&Weight::zero()), 0);
		assert_eq!(Poly::weight_to_fee(&Weight::from_ref_time(10)), 0);
	}

	#[test]
	fn polynomial_does_not_overflow() {
		assert_eq!(Poly::weight_to_fee(&Weight::MAX), Balance::max_value() - 10_000);
	}

	#[test]
	fn identity_fee_works() {
		assert_eq!(IdentityFee::<Balance>::weight_to_fee(&Weight::zero()), 0);
		assert_eq!(IdentityFee::<Balance>::weight_to_fee(&Weight::from_ref_time(50)), 50);
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
			ConstantMultiplier::<u128, ConstU128<10u128>>::weight_to_fee(&Weight::from_ref_time(
				50
			)),
			500
		);
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<1024u128>>::weight_to_fee(&Weight::from_ref_time(
				16
			)),
			16384
		);
		assert_eq!(
			ConstantMultiplier::<u128, ConstU128<{ u128::MAX }>>::weight_to_fee(
				&Weight::from_ref_time(2)
			),
			u128::MAX
		);
	}
}
