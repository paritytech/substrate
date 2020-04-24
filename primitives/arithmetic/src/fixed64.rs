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

use sp_std::{
	ops, prelude::*,
	convert::{TryFrom, TryInto},
};
use codec::{Encode, Decode};
use num_traits::Signed;
use crate::{
	helpers_128bit::{multiply_by_rational, multiply},
	PerThing, Perbill,
	traits::{
		SaturatedConversion, CheckedSub, CheckedAdd, CheckedMul, CheckedDiv,
		Bounded, UniqueSaturatedInto, Saturating, FixedPointNumber, BaseArithmetic
	},
	implement_fixed
};
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

implement_fixed!(
	Fixed64,
	i64,
	u64,
	u32,
	Perbill,
	30,
	9,
);

// #[cfg(test)]
// mod tests {
// 	use super::*;
// 	use crate::{Perbill, Percent, Permill, Perquintill};

// 	fn max() -> Fixed64 {
// 		Fixed64::max_value()
// 	}

// 	fn min() -> Fixed64 {
// 		Fixed64::min_value()
// 	}

// 	#[test]
// 	fn fixed64_semantics() {
// 		let a = Fixed64::checked_from_rational(5, 2).unwrap();
// 		let b = Fixed64::checked_from_rational(10, 4).unwrap();
// 		assert_eq!(a.0, 5 * Fixed64::DIV / 2);
// 		assert_eq!(a, b);

// 		let a = Fixed64::checked_from_rational(-5, 1).unwrap();
// 		assert_eq!(a, Fixed64::from_integer(-5));

// 		// biggest value that can be created.
// 		assert_eq!(max(), Fixed64::from_inner(9_223_372_036_854_775_807));

// 		// the smallest value that can be created.
// 		assert_eq!(min(), Fixed64::from_inner(-9_223_372_036_854_775_808));
// 	}


// 	#[test]
// 	fn from_rational_works() {
// 		let a = Fixed64::checked_from_rational(100_000_000_000_000_000i64, 1_000_000_000_000_000_000i64);
// 		assert_eq!(a, None);
// 	}

// 	#[test]
// 	fn fixed64_operation() {
// 		let a = Fixed64::from_integer(2);
// 		let b = Fixed64::from_integer(1);
// 		assert_eq!(a.checked_add(&b), Some(Fixed64::from_integer(1 + 2)));
// 		assert_eq!(a.checked_sub(&b), Some(Fixed64::from_integer(2 - 1)));
// 		assert_eq!(a.checked_mul(&b), Some(Fixed64::from_integer(1 * 2)));
// 		assert_eq!(
// 			a.checked_div(&b),
// 			Some(Fixed64::checked_from_rational(2, 1).unwrap())
// 		);

// 		let a = Fixed64::checked_from_rational(5, 2).unwrap();
// 		let b = Fixed64::checked_from_rational(3, 2).unwrap();
// 		assert_eq!(
// 			a.checked_add(&b),
// 			Some(Fixed64::checked_from_rational(8, 2).unwrap())
// 		);
// 		assert_eq!(
// 			a.checked_sub(&b),
// 			Some(Fixed64::checked_from_rational(2, 2).unwrap())
// 		);
// 		assert_eq!(
// 			a.checked_mul(&b),
// 			Some(Fixed64::checked_from_rational(15, 4).unwrap())
// 		);
// 		assert_eq!(
// 			a.checked_div(&b),
// 			Some(Fixed64::checked_from_rational(10, 6).unwrap())
// 		);

// 		let a = Fixed64::from_integer(120);
// 		assert_eq!(a.checked_div_int(&2i32), Some(60));

// 		let a = Fixed64::checked_from_rational(20, 1).unwrap();
// 		assert_eq!(a.checked_div_int(&2i32), Some(10));

// 		let a = Fixed64::from_integer(120);
// 		assert_eq!(a.checked_mul_int(&2i32), Some(240));

// 		let a = Fixed64::checked_from_rational(1, 2).unwrap();
// 		assert_eq!(a.checked_mul_int(&20i32), Some(10));

// 		let a = Fixed64::checked_from_rational(-1, 2).unwrap();
// 		assert_eq!(a.checked_mul_int(&20i32), Some(-10));
// 	}

// 	#[test]
// 	fn checked_mul_should_work() {
// 		let a = Fixed64::from_integer(2);
// 		assert_eq!(min().checked_mul(&a), None);
// 		assert_eq!(max().checked_mul(&a), None);
// 	}

// 	#[test]
// 	fn checked_mul_int_should_work() {
// 		let a = Fixed64::from_integer(2);
// 		let b = Fixed64::from_integer(-1);

// 		assert_eq!(min().checked_mul_int(&2i8), None);
// 		assert_eq!(max().checked_mul_int(&2i8), None);

// 		assert_eq!(b.checked_mul_int(&i8::min_value()), None);
// 		assert_eq!(a.checked_mul_int(&i8::max_value()), None);
// 		assert_eq!(a.checked_mul_int(&i8::min_value()), None);

// 		let neg_result = (i64::min_value() as i128 * 2i128) / Fixed64::DIV as i128;
// 		let pos_result = (i64::max_value() as i128 * 2i128) / Fixed64::DIV as i128;
// 		assert_eq!(min().checked_mul_int(&2i128), Some(neg_result));
// 		assert_eq!(max().checked_mul_int(&2i128), Some(pos_result));
// 	}

// 	#[test]
// 	fn saturating_mul_should_work() {
// 		let a = Fixed64::from_integer(10);
// 		assert_eq!(min().saturating_mul(a), min());
// 		assert_eq!(max().saturating_mul(a), max());

// 		let b = Fixed64::from_integer(-1);
// 		assert_eq!(Fixed64::from_integer(125).saturating_mul(b).into_inner(), -125 * Fixed64::DIV);

// 		let c = Fixed64::checked_from_rational(1, 5).unwrap();
// 		assert_eq!(Fixed64::from_integer(125).saturating_mul(c).into_inner(), 25 * Fixed64::DIV);
// 	}

// 	#[test]
// 	fn saturating_mul_int_works() {
// 		let a = Fixed64::checked_from_rational(10, 1).unwrap();
// 		assert_eq!(a.saturating_mul_int(&i32::max_value()), i32::max_value());

// 		let a = Fixed64::checked_from_rational(-10, 1).unwrap();
// 		assert_eq!(a.saturating_mul_int(&i32::max_value()), i32::min_value());

// 		let a = Fixed64::checked_from_rational(3, 1).unwrap();
// 		assert_eq!(a.saturating_mul_int(&100i8), i8::max_value());

// 		let a = Fixed64::checked_from_rational(10, 1).unwrap();
// 		assert_eq!(a.saturating_mul_int(&123i128), 1230);

// 		let a = Fixed64::checked_from_rational(-10, 1).unwrap();
// 		assert_eq!(a.saturating_mul_int(&123i128), -1230);

// 		assert_eq!(max().saturating_mul_int(&2i128), 18_446_744_073);
// 		assert_eq!(min().saturating_mul_int(&2i128), -18_446_744_073);

// 		assert_eq!(max().saturating_mul_int(&i64::min_value()), i64::min_value());
// 		assert_eq!(min().saturating_mul_int(&i64::max_value()), i64::min_value());
// 		assert_eq!(min().saturating_mul_int(&i64::min_value()), i64::max_value());

// 		assert_eq!(max().saturating_mul_int(&i128::min_value()), i128::min_value());
// 		assert_eq!(min().saturating_mul_int(&i128::max_value()), i128::min_value());
// 		assert_eq!(min().saturating_mul_int(&i128::min_value()), i128::max_value());
// 	}

// 	#[test]
// 	fn zero_works() {
// 		assert_eq!(Fixed64::zero(), Fixed64::from_integer(0));
// 	}

// 	#[test]
// 	fn is_zero_works() {
// 		assert!(Fixed64::zero().is_zero());
// 		assert!(!Fixed64::from_integer(1).is_zero());
// 	}

// 	#[test]
// 	fn checked_div_with_zero_should_be_none() {
// 		let a = Fixed64::from_integer(1);
// 		let b = Fixed64::from_integer(0);

// 		assert_eq!(a.checked_div(&b), None);
// 		assert_eq!(b.checked_div(&a), Some(b));

// 		let c = Fixed64::from_integer(-1);

// 		assert_eq!((Fixed64::min_value() + Fixed64::checked_from_rational(1, Fixed64::accuracy()).unwrap()).checked_div(&c), Some(Fixed64::max_value()));
// 		assert_eq!(Fixed64::min_value().checked_div(&c), None);
// 		assert_eq!((Fixed64::one()).checked_div(&Fixed64::zero()), None);
// 	}

// 	#[test]
// 	fn checked_div_int_with_zero_should_be_none() {
// 		let a = Fixed64::from_integer(1);
// 		assert_eq!(a.checked_div_int(&0i32), None);
// 		let a = Fixed64::from_integer(0);
// 		assert_eq!(a.checked_div_int(&1i32), Some(0));
// 	}

// 	#[test]
// 	fn checked_div_with_zero_dividend_should_be_zero() {
// 		let a = Fixed64::zero();
// 		let b = Fixed64::from_inner(1);

// 		assert_eq!(a.checked_div(&b), Some(Fixed64::zero()));
// 	}

// 	#[test]
// 	fn under_flow_should_be_none() {
// 		let b = Fixed64::from_integer(1);
// 		assert_eq!(min().checked_sub(&b), None);
// 	}

// 	#[test]
// 	fn over_flow_should_be_none() {
// 		let a = Fixed64::from_inner(i64::max_value() - 1);
// 		let b = Fixed64::from_inner(2);
// 		assert_eq!(a.checked_add(&b), None);

// 		let a = Fixed64::max_value();
// 		let b = Fixed64::checked_from_rational(2, 1).unwrap();
// 		assert_eq!(a.checked_mul(&b), None);

// 		let a = Fixed64::from_integer(255);
// 		let b = 2u8;
// 		assert_eq!(a.checked_mul_int(&b), None);

// 		let a = Fixed64::from_integer(256);
// 		let b = 1u8;
// 		assert_eq!(a.checked_div_int(&b), None);

// 		let a = Fixed64::from_integer(256);
// 		let b = -1i8;
// 		assert_eq!(a.checked_div_int(&b), None);
// 	}

// 	#[test]
// 	fn checked_div_int_should_work() {
// 		// 256 / 10 = 25 (25.6 as int = 25)
// 		let a = Fixed64::from_integer(256);
// 		let result = a.checked_div_int(&10i128).unwrap();
// 		assert_eq!(result, 25);

// 		// 256 / 100 = 2 (2.56 as int = 2)
// 		let a = Fixed64::from_integer(256);
// 		let result = a.checked_div_int(&100i128).unwrap();
// 		assert_eq!(result, 2);

// 		// 256 / 1000 = 0 (0.256 as int = 0)
// 		let a = Fixed64::from_integer(256);
// 		let result = a.checked_div_int(&1000i128).unwrap();
// 		assert_eq!(result, 0);

// 		// 256 / -1 = -256
// 		let a = Fixed64::from_integer(256);
// 		let result = a.checked_div_int(&-1i128).unwrap();
// 		assert_eq!(result, -256);

// 		// -256 / -1 = 256
// 		let a = Fixed64::from_integer(-256);
// 		let result = a.checked_div_int(&-1i128).unwrap();
// 		assert_eq!(result, 256);

// 		// 10 / -5 = -2
// 		let a = Fixed64::checked_from_rational(20, 2).unwrap();
// 		let result = a.checked_div_int(&-5i128).unwrap();
// 		assert_eq!(result, -2);

// 		// -170_141_183_460_469_231_731 / -2 = 85_070_591_730_234_615_865
// 		let result = min().checked_div_int(&-2i128).unwrap();
// 		assert_eq!(result, (min().0 as i128 / -2i128) / Fixed64::DIV as i128);
// 	}

// 	#[test]
// 	fn perthing_into_fixed() {
// 		let ten_percent_percent: Fixed64 = Percent::from_percent(10).try_into().unwrap();
// 		assert_eq!(ten_percent_percent.into_inner(), Fixed64::DIV / 10);

// 		let ten_percent_permill: Fixed64 = Permill::from_percent(10).into();
// 		assert_eq!(ten_percent_permill.into_inner(), Fixed64::DIV / 10);

// 		let ten_percent_perbill: Fixed64 = Perbill::from_percent(10).into();
// 		assert_eq!(ten_percent_perbill.into_inner(), Fixed64::DIV / 10);
// 	}

// 	#[test]
// 	fn serialize_deserialize_should_work() {
// 		let two_point_five = Fixed64::checked_from_rational(5, 2).unwrap();
// 		let serialized = serde_json::to_string(&two_point_five).unwrap();
// 		assert_eq!(serialized, "\"2500000000\"");
// 		let deserialized: Fixed64 = serde_json::from_str(&serialized).unwrap();
// 		assert_eq!(deserialized, two_point_five);

// 		let minus_two_point_five = Fixed64::checked_from_rational(-5, 2).unwrap();
// 		let serialized = serde_json::to_string(&minus_two_point_five).unwrap();
// 		assert_eq!(serialized, "\"-2500000000\"");
// 		let deserialized: Fixed64 = serde_json::from_str(&serialized).unwrap();
// 		assert_eq!(deserialized, minus_two_point_five);
// 	}


// 	#[test]
// 	fn saturating_abs_should_work() {
// 		// normal
// 		assert_eq!(Fixed64::from_inner(1).saturating_abs(), Fixed64::from_inner(1));
// 		assert_eq!(Fixed64::from_inner(-1).saturating_abs(), Fixed64::from_inner(1));

// 		// saturating
// 		assert_eq!(Fixed64::min_value().saturating_abs(), Fixed64::max_value());
// 	}

// 	#[test]
// 	fn is_positive_negative_should_work() {
// 		let positive = Fixed64::from_inner(1);
// 		assert!(positive.is_positive());
// 		assert!(!positive.is_negative());

// 		let negative = Fixed64::from_inner(-1);
// 		assert!(!negative.is_positive());
// 		assert!(negative.is_negative());

// 		let zero = Fixed64::zero();
// 		assert!(!zero.is_positive());
// 		assert!(!zero.is_negative());
// 	}

// 	#[test]
// 	fn fmt_should_work() {
// 		let positive = Fixed64::from_inner(1000000000000000001);
// 		assert_eq!(format!("{:?}", positive), "Fixed64(1000000000.000000001)");
// 		let negative = Fixed64::from_inner(-1000000000000000001);
// 		assert_eq!(format!("{:?}", negative), "Fixed64(-1000000000.000000001)");

// 		let positive_fractional = Fixed64::from_inner(1);
// 		assert_eq!(format!("{:?}", positive_fractional), "Fixed64(0.000000001)");
// 		let negative_fractional = Fixed64::from_inner(-1);
// 		assert_eq!(format!("{:?}", negative_fractional), "Fixed64(-0.000000001)");

// 		let zero = Fixed64::zero();
// 		assert_eq!(format!("{:?}", zero), "Fixed64(0.000000000)");
// 	}


// 	#[test]
// 	fn recip_should_work() {
// 		let a = Fixed64::from_integer(2);
// 		assert_eq!(
// 			a.reciprocal(),
// 			Some(Fixed64::checked_from_rational(1, 2).unwrap())
// 		);

// 		let a = Fixed64::from_integer(2);
// 		assert_eq!(a.reciprocal().unwrap().checked_mul_int(&4i32), Some(2i32));

// 		let a = Fixed64::checked_from_rational(1, 2).unwrap();
// 		assert_eq!(a.reciprocal().unwrap().checked_mul(&a), Some(Fixed64::from_integer(1)));

// 		let a = Fixed64::from_integer(0);
// 		assert_eq!(a.reciprocal(), None);

// 		let a = Fixed64::checked_from_rational(-1, 2).unwrap();
// 		assert_eq!(a.reciprocal(), Some(Fixed64::from_integer(-2)));
// 	}

// 	#[test]
// 	fn fixed_64_growth_decrease_curve() {
// 		let test_set = vec![0u32, 1, 10, 1000, 1_000_000_000];

// 		// negative (1/2)
// 		let mut fm = Fixed64::checked_from_rational(-1, 2).unwrap();
// 		test_set.clone().into_iter().for_each(|i| {
// 			assert_eq!(fm.saturated_multiply_accumulate(i) as i32, i as i32 - i as i32 / 2);
// 		});

// 		// unit (1) multiplier
// 		fm = Fixed64::from_inner(0);
// 		test_set.clone().into_iter().for_each(|i| {
// 			assert_eq!(fm.saturated_multiply_accumulate(i), i);
// 		});

// 		// i.5 multiplier
// 		fm = Fixed64::checked_from_rational(1, 2).unwrap();
// 		test_set.clone().into_iter().for_each(|i| {
// 			assert_eq!(fm.saturated_multiply_accumulate(i), i * 3 / 2);
// 		});

// 		// dual multiplier
// 		fm = Fixed64::checked_from_rational(1, 1).unwrap();
// 		test_set.clone().into_iter().for_each(|i| {
// 			assert_eq!(fm.saturated_multiply_accumulate(i), i * 2);
// 		});
// 	}

// 	macro_rules! saturating_mul_acc_test {
// 		($num_type:tt) => {
// 			assert_eq!(
// 				Fixed64::checked_from_rational(100, 1).unwrap().saturated_multiply_accumulate(10 as $num_type),
// 				1010,
// 			);
// 			assert_eq!(
// 				Fixed64::checked_from_rational(100, 2).unwrap().saturated_multiply_accumulate(10 as $num_type),
// 				510,
// 			);
// 			assert_eq!(
// 				Fixed64::checked_from_rational(100, 3).unwrap().saturated_multiply_accumulate(0 as $num_type),
// 				0,
// 			);
// 			assert_eq!(
// 				Fixed64::checked_from_rational(5, 1).unwrap().saturated_multiply_accumulate($num_type::max_value()),
// 				$num_type::max_value()
// 			);
// 			assert_eq!(
// 				max().saturated_multiply_accumulate($num_type::max_value()),
// 				$num_type::max_value()
// 			);
// 		}
// 	}

// 	#[test]
// 	fn fixed64_multiply_accumulate_works() {
// 		saturating_mul_acc_test!(u32);
// 		saturating_mul_acc_test!(u64);
// 		saturating_mul_acc_test!(u128);
// 	}

// 	#[test]
// 	fn div_works() {
// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(10, 1).unwrap();
// 		println!("{:?} {:?}", a, b);
// 		assert_eq!(a / b, Fixed64::checked_from_rational(12, 100).unwrap());

// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(1, 100).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(120, 1).unwrap());

// 		let a = Fixed64::checked_from_rational(12, 100).unwrap();
// 		let b = Fixed64::checked_from_rational(10, 1).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(12, 1000).unwrap());

// 		let a = Fixed64::checked_from_rational(12, 100).unwrap();
// 		let b = Fixed64::checked_from_rational(1, 100).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(12, 1).unwrap());

// 		let a = Fixed64::checked_from_rational(-12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(10, 1).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(-12, 100).unwrap());

// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(-10, 1).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(-12, 100).unwrap());

// 		let a = Fixed64::checked_from_rational(-12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(-10, 1).unwrap();
// 		assert_eq!(a / b, Fixed64::checked_from_rational(12, 100).unwrap());
// 	}

// 	#[test]
// 	#[should_panic(expected = "attempt to divide by zero")]
// 	fn div_zero() {
// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::from_integer(0);
// 		let _ = a / b;
// 	}

// 	#[test]
// 	fn checked_div_zero() {
// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::from_integer(0);
// 		assert_eq!(a.checked_div(&b), None);
// 	}

// 	#[test]
// 	fn checked_div_non_zero() {
// 		let a = Fixed64::checked_from_rational(12, 10).unwrap();
// 		let b = Fixed64::checked_from_rational(1, 100).unwrap();
// 		assert_eq!(a.checked_div(&b), Some(Fixed64::checked_from_rational(120, 1).unwrap()));
// 	}

// 	#[test]
// 	fn saturating_pow_should_work() {
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(0), Fixed64::from_integer(1));
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(1), Fixed64::from_integer(2));
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(2), Fixed64::from_integer(4));
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(3), Fixed64::from_integer(8));
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(33), Fixed64::from_integer(8589934592));

// 		// Saturating.
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(49), Fixed64::from_integer(562949953421312));

// 		assert_eq!(Fixed64::from_integer(1).saturating_pow(1000), Fixed64::from_integer(1));
// 		assert_eq!(Fixed64::from_integer(-1).saturating_pow(1000), Fixed64::from_integer(1));
// 		assert_eq!(Fixed64::from_integer(-1).saturating_pow(1001), Fixed64::from_integer(-1));
// 		assert_eq!(Fixed64::from_integer(1).saturating_pow(usize::max_value()), Fixed64::from_integer(1));
// 		assert_eq!(Fixed64::from_integer(-1).saturating_pow(usize::max_value()), Fixed64::from_integer(-1));
// 		assert_eq!(Fixed64::from_integer(-1).saturating_pow(usize::max_value() - 1), Fixed64::from_integer(1));

// 		assert_eq!(Fixed64::from_integer(114209).saturating_pow(3), Fixed64::from_integer(1489707440031329));
// 		assert_eq!(Fixed64::from_integer(114209).saturating_pow(4), Fixed64::max_value());

// 		assert_eq!(Fixed64::from_integer(1).saturating_pow(usize::max_value()), Fixed64::from_integer(1));
// 		assert_eq!(Fixed64::from_integer(0).saturating_pow(usize::max_value()), Fixed64::from_integer(0));
// 		assert_eq!(Fixed64::from_integer(2).saturating_pow(usize::max_value()), Fixed64::max_value());
// 	}
// }
