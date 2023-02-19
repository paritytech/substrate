// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// Some code is based upon Derek Dreery's IntegerSquareRoot impl, used under license.
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

//! Some helper functions to work with 128bit numbers. Note that the functionality provided here is
//! only sensible to use with 128bit numbers because for smaller sizes, you can always rely on
//! assumptions of a bigger type (u128) being available, or simply create a per-thing and use the
//! multiplication implementation provided there.

use crate::{biguint, Rounding};
use sp_std::cmp::{max, min};

/// Helper gcd function used in Rational128 implementation.
pub fn gcd(a: u128, b: u128) -> u128 {
	match ((a, b), (a & 1, b & 1)) {
		((x, y), _) if x == y => y,
		((0, x), _) | ((x, 0), _) => x,
		((x, y), (0, 1)) | ((y, x), (1, 0)) => gcd(x >> 1, y),
		((x, y), (0, 0)) => gcd(x >> 1, y >> 1) << 1,
		((x, y), (1, 1)) => {
			let (x, y) = (min(x, y), max(x, y));
			gcd((y - x) >> 1, x)
		},
		_ => unreachable!(),
	}
}

/// split a u128 into two u64 limbs
pub fn split(a: u128) -> (u64, u64) {
	let al = a as u64;
	let ah = (a >> 64) as u64;
	(ah, al)
}

/// Convert a u128 to a u32 based biguint.
pub fn to_big_uint(x: u128) -> biguint::BigUint {
	let (xh, xl) = split(x);
	let (xhh, xhl) = biguint::split(xh);
	let (xlh, xll) = biguint::split(xl);
	let mut n = biguint::BigUint::from_limbs(&[xhh, xhl, xlh, xll]);
	n.lstrip();
	n
}

mod double128 {
	// Inspired by: https://medium.com/wicketh/mathemagic-512-bit-division-in-solidity-afa55870a65

	/// Returns the least significant 64 bits of a
	const fn low_64(a: u128) -> u128 {
		a & ((1 << 64) - 1)
	}

	/// Returns the most significant 64 bits of a
	const fn high_64(a: u128) -> u128 {
		a >> 64
	}

	/// Returns 2^128 - a (two's complement)
	const fn neg128(a: u128) -> u128 {
		(!a).wrapping_add(1)
	}

	/// Returns 2^128 / a
	const fn div128(a: u128) -> u128 {
		(neg128(a) / a).wrapping_add(1)
	}

	/// Returns 2^128 % a
	const fn mod128(a: u128) -> u128 {
		neg128(a) % a
	}

	#[derive(Copy, Clone, Eq, PartialEq)]
	pub struct Double128 {
		high: u128,
		low: u128,
	}

	impl Double128 {
		pub const fn try_into_u128(self) -> Result<u128, ()> {
			match self.high {
				0 => Ok(self.low),
				_ => Err(()),
			}
		}

		pub const fn zero() -> Self {
			Self { high: 0, low: 0 }
		}

		/// Return a `Double128` value representing the `scaled_value << 64`.
		///
		/// This means the lower half of the `high` component will be equal to the upper 64-bits of
		/// `scaled_value` (in the lower positions) and the upper half of the `low` component will
		/// be equal to the lower 64-bits of `scaled_value`.
		pub const fn left_shift_64(scaled_value: u128) -> Self {
			Self { high: scaled_value >> 64, low: scaled_value << 64 }
		}

		/// Construct a value from the upper 128 bits only, with the lower being zeroed.
		pub const fn from_low(low: u128) -> Self {
			Self { high: 0, low }
		}

		/// Returns the same value ignoring anything in the high 128-bits.
		pub const fn low_part(self) -> Self {
			Self { high: 0, ..self }
		}

		/// Returns a*b (in 256 bits)
		pub const fn product_of(a: u128, b: u128) -> Self {
			// Split a and b into hi and lo 64-bit parts
			let (a_low, a_high) = (low_64(a), high_64(a));
			let (b_low, b_high) = (low_64(b), high_64(b));
			// a = (a_low + a_high << 64); b = (b_low + b_high << 64);
			// ergo a*b = (a_low + a_high << 64)(b_low + b_high << 64)
			//          = a_low * b_low
			//          + a_low * b_high << 64
			//          + a_high << 64 * b_low
			//          + a_high << 64 * b_high << 64
			// assuming:
			//        f = a_low * b_low
			//        o = a_low * b_high
			//        i = a_high * b_low
			//        l = a_high * b_high
			// then:
			//      a*b = (o+i) << 64 + f + l << 128
			let (f, o, i, l) = (a_low * b_low, a_low * b_high, a_high * b_low, a_high * b_high);
			let fl = Self { high: l, low: f };
			let i = Self::left_shift_64(i);
			let o = Self::left_shift_64(o);
			fl.add(i).add(o)
		}

		pub const fn add(self, b: Self) -> Self {
			let (low, overflow) = self.low.overflowing_add(b.low);
			let carry = overflow as u128; // 1 if true, 0 if false.
			let high = self.high.wrapping_add(b.high).wrapping_add(carry as u128);
			Double128 { high, low }
		}

		pub const fn div(mut self, rhs: u128) -> (Self, u128) {
			if rhs == 1 {
				return (self, 0)
			}

			// (self === a; rhs === b)
			// Calculate a / b
			// = (a_high << 128 + a_low) / b
			//   let (q, r) = (div128(b), mod128(b));
			// = (a_low * (q * b + r)) + a_high) / b
			// = (a_low * q * b + a_low * r + a_high)/b
			// = (a_low * r + a_high) / b + a_low * q
			let (q, r) = (div128(rhs), mod128(rhs));

			// x = current result
			// a = next number
			let mut x = Self::zero();
			while self.high != 0 {
				// x += a.low * q
				x = x.add(Self::product_of(self.high, q));
				// a = a.low * r + a.high
				self = Self::product_of(self.high, r).add(self.low_part());
			}

			(x.add(Self::from_low(self.low / rhs)), self.low % rhs)
		}
	}
}

/// Returns `a * b / c` and `(a * b) % c` (wrapping to 128 bits) or `None` in the case of
/// overflow and c = 0.
pub const fn multiply_by_rational_with_rounding(
	a: u128,
	b: u128,
	c: u128,
	r: Rounding,
) -> Option<u128> {
	use double128::Double128;
	if c == 0 {
		return None
	}
	let (result, remainder) = Double128::product_of(a, b).div(c);
	let mut result: u128 = match result.try_into_u128() {
		Ok(v) => v,
		Err(_) => return None,
	};
	if match r {
		Rounding::Up => remainder > 0,
		// cannot be `(c + 1) / 2` since `c` might be `max_value` and overflow.
		Rounding::NearestPrefUp => remainder >= c / 2 + c % 2,
		Rounding::NearestPrefDown => remainder > c / 2,
		Rounding::Down => false,
	} {
		result = match result.checked_add(1) {
			Some(v) => v,
			None => return None,
		};
	}
	Some(result)
}

pub const fn sqrt(mut n: u128) -> u128 {
	// Modified from https://github.com/derekdreery/integer-sqrt-rs (Apache/MIT).
	if n == 0 {
		return 0
	}

	// Compute bit, the largest power of 4 <= n
	let max_shift: u32 = 0u128.leading_zeros() - 1;
	let shift: u32 = (max_shift - n.leading_zeros()) & !1;
	let mut bit = 1u128 << shift;

	// Algorithm based on the implementation in:
	// https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)
	// Note that result/bit are logically unsigned (even if T is signed).
	let mut result = 0u128;
	while bit != 0 {
		if n >= result + bit {
			n -= result + bit;
			result = (result >> 1) + bit;
		} else {
			result = result >> 1;
		}
		bit = bit >> 2;
	}
	result
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Decode, Encode};
	use multiply_by_rational_with_rounding as mulrat;
	use Rounding::*;

	const MAX: u128 = u128::max_value();

	#[test]
	fn rational_multiply_basic_rounding_works() {
		assert_eq!(mulrat(1, 1, 1, Up), Some(1));
		assert_eq!(mulrat(3, 1, 3, Up), Some(1));
		assert_eq!(mulrat(1, 1, 3, Up), Some(1));
		assert_eq!(mulrat(1, 2, 3, Down), Some(0));
		assert_eq!(mulrat(1, 1, 3, NearestPrefDown), Some(0));
		assert_eq!(mulrat(1, 1, 2, NearestPrefDown), Some(0));
		assert_eq!(mulrat(1, 2, 3, NearestPrefDown), Some(1));
		assert_eq!(mulrat(1, 1, 3, NearestPrefUp), Some(0));
		assert_eq!(mulrat(1, 1, 2, NearestPrefUp), Some(1));
		assert_eq!(mulrat(1, 2, 3, NearestPrefUp), Some(1));
	}

	#[test]
	fn rational_multiply_big_number_works() {
		assert_eq!(mulrat(MAX, MAX - 1, MAX, Down), Some(MAX - 1));
		assert_eq!(mulrat(MAX, 1, MAX, Down), Some(1));
		assert_eq!(mulrat(MAX, MAX - 1, MAX, Up), Some(MAX - 1));
		assert_eq!(mulrat(MAX, 1, MAX, Up), Some(1));
		assert_eq!(mulrat(1, MAX - 1, MAX, Down), Some(0));
		assert_eq!(mulrat(1, 1, MAX, Up), Some(1));
		assert_eq!(mulrat(1, MAX / 2, MAX, NearestPrefDown), Some(0));
		assert_eq!(mulrat(1, MAX / 2 + 1, MAX, NearestPrefDown), Some(1));
		assert_eq!(mulrat(1, MAX / 2, MAX, NearestPrefUp), Some(0));
		assert_eq!(mulrat(1, MAX / 2 + 1, MAX, NearestPrefUp), Some(1));
	}

	#[test]
	fn sqrt_works() {
		for i in 0..100_000u32 {
			let a = sqrt(random_u128(i));
			assert_eq!(sqrt(a * a), a);
		}
	}

	fn random_u128(seed: u32) -> u128 {
		u128::decode(&mut &seed.using_encoded(sp_core::hashing::twox_128)[..]).unwrap_or(0)
	}

	#[test]
	fn op_checked_rounded_div_works() {
		for i in 0..100_000u32 {
			let a = random_u128(i);
			let b = random_u128(i + (1 << 30));
			let c = random_u128(i + (1 << 31));
			let x = mulrat(a, b, c, NearestPrefDown);
			let y = multiply_by_rational_with_rounding(a, b, c, Rounding::NearestPrefDown);
			assert_eq!(x.is_some(), y.is_some());
			let x = x.unwrap_or(0);
			let y = y.unwrap_or(0);
			let d = x.max(y) - x.min(y);
			assert_eq!(d, 0);
		}
	}
}
