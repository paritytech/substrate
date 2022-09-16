// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Infinite precision unsigned integer for substrate runtime.

use num_traits::{Zero, One};
use sp_std::{cmp::Ordering, ops, prelude::*, vec, cell::RefCell, convert::TryFrom};

// A sensible value for this would be half of the dword size of the host machine. Since the
// runtime is compiled to 32bit webassembly, using 32 and 64 for single and double respectively
// should yield the most performance.

/// Representation of a single limb.
pub type Single = u32;
/// Representation of two limbs.
pub type Double = u64;
/// Difference in the number of bits of [`Single`] and [`Double`].
const SHIFT: usize = 32;
/// short form of _Base_. Analogous to the value 10 in base-10 decimal numbers.
const B: Double = Single::max_value() as Double + 1;

static_assertions::const_assert!(
	sp_std::mem::size_of::<Double>() - sp_std::mem::size_of::<Single>() == SHIFT / 8
);

/// Splits a [`Double`] limb number into a tuple of two [`Single`] limb numbers.
pub fn split(a: Double) -> (Single, Single) {
	let al = a as Single;
	let ah = (a >> SHIFT) as Single;
	(ah, al)
}

/// Assumed as a given primitive.
///
/// Multiplication of two singles, which at most yields 1 double.
pub fn mul_single(a: Single, b: Single) -> Double {
	let a: Double = a.into();
	let b: Double = b.into();
	a * b
}

/// Assumed as a given primitive.
///
/// Addition of two singles, which at most takes a single limb of result and a carry,
/// returned as a tuple respectively.
pub fn add_single(a: Single, b: Single) -> (Single, Single) {
	let a: Double = a.into();
	let b: Double = b.into();
	let q = a + b;
	let (carry, r) = split(q);
	(r, carry)
}

/// Assumed as a given primitive.
///
/// Division of double by a single limb. Always returns a double limb of quotient and a single
/// limb of remainder.
fn div_single(a: Double, b: Single) -> (Double, Single) {
	let b: Double = b.into();
	let q = a / b;
	let r = a % b;
	// both conversions are trivially safe.
	(q, r as Single)
}

/// Simple wrapper around an infinitely large integer, represented as limbs of [`Single`].
#[derive(Clone, Default)]
pub struct BigUint {
	/// digits (limbs) of this number (sorted as msb -> lsb).
	pub(crate) digits: Vec<Single>,
}

impl BigUint {
	/// Create a new instance with `size` limbs. This prevents any number with zero limbs to be
	/// created.
	///
	/// The behavior of the type is undefined with zero limbs.
	pub fn with_capacity(size: usize) -> Self {
		Self { digits: vec![0; size.max(1)] }
	}

	/// Raw constructor from custom limbs. If `limbs` is empty, `Zero::zero()` implementation is
	/// used.
	pub fn from_limbs(limbs: &[Single]) -> Self {
		if !limbs.is_empty() {
			Self { digits: limbs.to_vec() }
		} else {
			Zero::zero()
		}
	}

	/// Number of limbs.
	pub fn len(&self) -> usize { self.digits.len() }

	/// A naive getter for limb at `index`. Note that the order is lsb -> msb.
	///
	/// #### Panics
	///
	/// This panics if index is out of range.
	pub fn get(&self, index: usize) -> Single {
		self.digits[self.len() - 1 - index]
	}

	/// A naive getter for limb at `index`. Note that the order is lsb -> msb.
	pub fn checked_get(&self, index: usize) -> Option<Single> {
		let i = self.len().checked_sub(1)?;
		let j = i.checked_sub(index)?;
		self.digits.get(j).cloned()
	}

	/// A naive setter for limb at `index`. Note that the order is lsb -> msb.
	///
	/// #### Panics
	///
	/// This panics if index is out of range.
	pub fn set(&mut self, index: usize, value: Single) {
		let len = self.digits.len();
		self.digits[len - 1 - index] = value;
	}

	/// returns the least significant limb of the number.
	///
	/// #### Panics
	///
	/// While the constructor of the type prevents this, this can panic if `self` has no digits.
	pub fn lsb(&self) -> Single {
		self.digits[self.len() - 1]
	}

	/// returns the most significant limb of the number.
	///
	/// #### Panics
	///
	/// While the constructor of the type prevents this, this can panic if `self` has no digits.
	pub fn msb(&self) -> Single {
		self.digits[0]
	}

	/// Strips zeros from the left side (the most significant limbs) of `self`, if any.
	pub fn lstrip(&mut self) {
		// by definition, a big-int number should never have leading zero limbs. This function
		// has the ability to cause this. There is nothing to do if the number already has 1
		// limb only. call it a day and return.
		if self.len().is_zero() { return; }
		let index = self.digits.iter().position(|&elem| elem != 0).unwrap_or(self.len() - 1);

		if index > 0 {
			self.digits = self.digits[index..].to_vec()
		}
	}

	/// Zero-pad `self` from left to reach `size` limbs. Will not make any difference if `self`
	/// is already bigger than `size` limbs.
	pub fn lpad(&mut self, size: usize) {
		let n = self.len();
		if n >= size { return; }
		let pad = size - n;
		let mut new_digits = (0..pad).map(|_| 0).collect::<Vec<Single>>();
		new_digits.extend(self.digits.iter());
		self.digits = new_digits;
	}

	/// Adds `self` with `other`. self and other do not have to have any particular size. Given
	/// that the `n = max{size(self), size(other)}`, it will produce a number with `n + 1`
	/// limbs.
	///
	/// This function does not strip the output and returns the original allocated `n + 1`
	/// limbs. The caller may strip the output if desired.
	///
	/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
	pub fn add(self, other: &Self) -> Self {
		let n = self.len().max(other.len());
		let mut k: Double = 0;
		let mut w = Self::with_capacity(n + 1);

		for j in 0..n {
			let u = Double::from(self.checked_get(j).unwrap_or(0));
			let v = Double::from(other.checked_get(j).unwrap_or(0));
			let s = u + v + k;
			// proof: any number % B will fit into `Single`.
			w.set(j, (s % B) as Single);
			k = s / B;
		}
		// k is always 0 or 1.
		w.set(n, k as Single);
		w
	}

	/// Subtracts `other` from `self`. self and other do not have to have any particular size.
	/// Given that the `n = max{size(self), size(other)}`, it will produce a number of size `n`.
	///
	/// If `other` is bigger than `self`, `Err(B - borrow)` is returned.
	///
	/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
	pub fn sub(self, other: &Self) -> Result<Self, Self> {
		let n = self.len().max(other.len());
		let mut k = 0;
		let mut w = Self::with_capacity(n);
		for j in 0..n {
			let s = {
				let u = Double::from(self.checked_get(j).unwrap_or(0));
				let v = Double::from(other.checked_get(j).unwrap_or(0));

				if let Some(v2) = u.checked_sub(v).and_then(|v1| v1.checked_sub(k)) {
					// no borrow is needed. u - v - k can be computed as-is
					let t = v2;
					k = 0;

					t
				} else {
					// borrow is needed. Add a `B` to u, before subtracting.
					// PROOF: addition: `u + B < 2*B`, thus can fit in double.
					// PROOF: subtraction: if `u - v - k < 0`, then `u + B - v - k < B`.
					// NOTE: the order of operations is critical to ensure underflow won't happen.
					let t = u + B - v - k;
					k = 1;

					t
				}
			};
			w.set(j, s as Single);
		}

		if k.is_zero() {
			Ok(w)
		} else {
			Err(w)
		}
	}

	/// Multiplies n-limb number `self` with m-limb number `other`.
	///
	/// The resulting number will always have `n + m` limbs.
	///
	/// This function does not strip the output and returns the original allocated `n + m`
	/// limbs. The caller may strip the output if desired.
	///
	/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
	pub fn mul(self, other: &Self) -> Self {
		let n = self.len();
		let m = other.len();
		let mut w = Self::with_capacity(m + n);

		for j in 0..n {
			if self.get(j) == 0 {
				// Note: `with_capacity` allocates with 0. Explicitly set j + m to zero if
				// otherwise.
				continue;
			}

			let mut k = 0;
			for i in 0..m {
				// PROOF: (B−1) × (B−1) + (B−1) + (B−1) = B^2 −1 < B^2. addition is safe.
				let t = mul_single(self.get(j), other.get(i))
					+ Double::from(w.get(i + j))
					+ Double::from(k);
				w.set(i + j, (t % B) as Single);
				// PROOF: (B^2 - 1) / B < B. conversion is safe.
				k = (t / B) as Single;
			}
			w.set(j + m, k);
		}
		w
	}

	/// Divides `self` by a single limb `other`. This can be used in cases where the original
	/// division cannot work due to the divisor (`other`) being just one limb.
	///
	/// Invariant: `other` cannot be zero.
	pub fn div_unit(self, mut other: Single) -> Self {
		other = other.max(1);
		let n = self.len();
		let mut out = Self::with_capacity(n);
		let mut r: Single = 0;
		// PROOF: (B-1) * B + (B-1) still fits in double
		let with_r = |x: Single, r: Single| { Double::from(r) * B + Double::from(x) };
		for d in (0..n).rev() {
			let (q, rr) = div_single(with_r(self.get(d), r), other) ;
			out.set(d, q as Single);
			r = rr;
		}
		out
	}

	/// Divides an `n + m` limb self by a `n` limb `other`. The result is a `m + 1` limb
	/// quotient and a `n` limb remainder, if enabled by passing `true` in `rem` argument, both
	/// in the form of an option's `Ok`.
	///
	/// - requires `other` to be stripped and have no leading zeros.
	/// - requires `self` to be stripped and have no leading zeros.
	/// - requires `other` to have at least two limbs.
	/// - requires `self` to have a greater length compared to `other`.
	///
	/// All arguments are examined without being stripped for the above conditions. If any of
	/// the above fails, `None` is returned.`
	///
	/// Taken from "The Art of Computer Programming" by D.E. Knuth, vol 2, chapter 4.
	pub fn div(self, other: &Self, rem: bool) -> Option<(Self, Self)> {
		if other.len() <= 1
			|| other.msb() == 0
			|| self.msb() == 0
			|| self.len() <= other.len()
		{
			return None
		}
		let n = other.len();
		let m = self.len() - n;

		let mut q = Self::with_capacity(m + 1);
		let mut r = Self::with_capacity(n);

		// PROOF: 0 <= normalizer_bits < SHIFT 0 <= normalizer < B. all conversions are
		// safe.
		let normalizer_bits = other.msb().leading_zeros() as Single;
		let normalizer = 2_u32.pow(normalizer_bits as u32) as Single;

		// step D1.
		let mut self_norm = self.mul(&Self::from(normalizer));
		let mut other_norm = other.clone().mul(&Self::from(normalizer));

		// defensive only; the mul implementation should always create this.
		self_norm.lpad(n + m + 1);
		other_norm.lstrip();

		// step D2.
		for j in (0..=m).rev() {
			// step D3.0 Find an estimate of q[j], named qhat.
			let (qhat, rhat) = {
				// PROOF: this always fits into `Double`. In the context of Single = u8, and
				// Double = u16, think of 255 * 256 + 255 which is just u16::max_value().
				let dividend =
					Double::from(self_norm.get(j + n))
						* B
						+ Double::from(self_norm.get(j + n - 1));
				let divisor = other_norm.get(n - 1);
				div_single(dividend, divisor)
			};

			// D3.1 test qhat
			// replace qhat and rhat with RefCells. This helps share state with the closure
			let qhat = RefCell::new(qhat);
			let rhat = RefCell::new(Double::from(rhat));

			let test = || {
				// decrease qhat if it is bigger than the base (B)
				let qhat_local = *qhat.borrow();
				let rhat_local = *rhat.borrow();
				let predicate_1 = qhat_local >= B;
				let predicate_2 = {
					let lhs = qhat_local * Double::from(other_norm.get(n - 2));
					let rhs = B * rhat_local + Double::from(self_norm.get(j + n - 2));
					lhs > rhs
				};
				if predicate_1 || predicate_2 {
					*qhat.borrow_mut() -= 1;
					*rhat.borrow_mut() += Double::from(other_norm.get(n - 1));
					true
				} else {
					false
				}
			};

			test();
			while (*rhat.borrow() as Double) < B {
				if !test() { break; }
			}

			let qhat = qhat.into_inner();
			// we don't need rhat anymore. just let it go out of scope when it does.

			// step D4
			let lhs = Self { digits: (j..=j+n).rev().map(|d| self_norm.get(d)).collect() };
			let rhs = other_norm.clone().mul(&Self::from(qhat));

			let maybe_sub = lhs.sub(&rhs);
			let mut negative = false;
			let sub = match maybe_sub {
				Ok(t) => t,
				Err(t) => { negative = true; t }
			};
			(j..=j+n).for_each(|d| { self_norm.set(d, sub.get(d - j)); });

			// step D5
			// PROOF: the `test()` specifically decreases qhat until it is below `B`. conversion
			// is safe.
			q.set(j, qhat as Single);

			// step D6: add back if negative happened.
			if negative {
				q.set(j, q.get(j) - 1);
				let u = Self { digits: (j..=j+n).rev().map(|d| self_norm.get(d)).collect() };
				let r = other_norm.clone().add(&u);
				(j..=j+n).rev().for_each(|d| { self_norm.set(d, r.get(d - j)); })
			}
		}

		// if requested, calculate remainder.
		if rem {
			// undo the normalization.
			if normalizer_bits > 0 {
				let s = SHIFT as u32;
				let nb = normalizer_bits;
				for d in 0..n-1 {
					let v = self_norm.get(d) >> nb
						| self_norm.get(d + 1).overflowing_shl(s - nb).0;
					r.set(d, v);
				}
				r.set(n - 1, self_norm.get(n - 1) >> normalizer_bits);
			} else {
				r = self_norm;
			}
		}

		Some((q, r))
	}
}

impl sp_std::fmt::Debug for BigUint {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(
			f,
			"BigUint {{ {:?} ({:?})}}",
			self.digits,
			u128::try_from(self.clone()).unwrap_or(0),
		)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		Ok(())
	}

}

impl PartialEq for BigUint {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == Ordering::Equal
	}
}

impl Eq for BigUint {}

impl Ord for BigUint {
	fn cmp(&self, other: &Self) -> Ordering {
		let lhs_first = self.digits.iter().position(|&e| e != 0);
		let rhs_first = other.digits.iter().position(|&e| e != 0);

		match (lhs_first, rhs_first) {
			// edge cases that should not happen. This basically means that one or both were
			// zero.
			(None, None) => Ordering::Equal,
			(Some(_), None) => Ordering::Greater,
			(None, Some(_)) => Ordering::Less,
			(Some(lhs_idx), Some(rhs_idx)) => {
				let lhs = &self.digits[lhs_idx..];
				let rhs = &other.digits[rhs_idx..];
				let len_cmp = lhs.len().cmp(&rhs.len());
				match len_cmp {
					Ordering::Equal => lhs.cmp(rhs),
					_ => len_cmp,
				}
			}
		}
	}
}

impl PartialOrd for BigUint {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl ops::Add for BigUint {
	type Output = Self;
	fn add(self, rhs: Self) -> Self::Output {
		self.add(&rhs)
	}
}

impl ops::Sub for BigUint {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self::Output {
		self.sub(&rhs).unwrap_or_else(|e| e)
	}
}

impl ops::Mul for BigUint {
	type Output = Self;
	fn mul(self, rhs: Self) -> Self::Output {
		self.mul(&rhs)
	}
}

impl Zero for BigUint {
	fn zero() -> Self {
		Self { digits: vec![Zero::zero()] }
	}

	fn is_zero(&self) -> bool {
		self.digits.iter().all(|d| d.is_zero())
	}
}

impl One for BigUint {
	fn one() -> Self {
		Self { digits: vec![Single::one()] }
	}
}

macro_rules! impl_try_from_number_for {
	($([$type:ty, $len:expr]),+) => {
		$(
			impl TryFrom<BigUint> for $type {
				type Error = &'static str;
				fn try_from(mut value: BigUint) -> Result<$type, Self::Error> {
					value.lstrip();
					let error_message = concat!("cannot fit a number into ", stringify!($type));
					if value.len() * SHIFT > $len {
						Err(error_message)
					} else {
						let mut acc: $type = Zero::zero();
						for (i, d) in value.digits.iter().rev().cloned().enumerate() {
							let d: $type = d.into();
							acc += d << (SHIFT * i);
						}
						Ok(acc)
					}
				}
			}
		)*
	};
}
// can only be implemented for sizes bigger than two limb.
impl_try_from_number_for!([u128, 128], [u64, 64]);

macro_rules! impl_from_for_smaller_than_word {
	($($type:ty),+) => {
		$(impl From<$type> for BigUint {
			fn from(a: $type) -> Self {
				Self { digits: vec! [a.into()] }
			}
		})*
	}
}
impl_from_for_smaller_than_word!(u8, u16, u32);

impl From<u64> for BigUint {
	fn from(a: Double) -> Self {
		let (ah, al) = split(a);
		Self { digits: vec![ah, al] }
	}
}

impl From<u128> for BigUint {
	fn from(a: u128) -> Self {
		crate::helpers_128bit::to_big_uint(a)
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;

	fn with_limbs(n: usize) -> BigUint {
		BigUint { digits: vec![1; n] }
	}

	#[test]
	fn split_works() {
		let a = SHIFT / 2;
		let b = SHIFT * 3 / 2;
		let num: Double = 1 << a | 1 << b;
		assert_eq!(num, 0x_0001_0000_0001_0000);
		assert_eq!(split(num), (1 << a, 1 << a));

		let a = SHIFT / 2 + 4;
		let b = SHIFT / 2 - 4;
		let num: Double = 1 << (SHIFT + a) | 1 << b;
		assert_eq!(num, 0x_0010_0000_0000_1000);
		assert_eq!(split(num), (1 << a, 1 << b));
	}

	#[test]
	fn strip_works() {
		let mut a = BigUint::from_limbs(&[0, 1, 0]);
		a.lstrip();
		assert_eq!(a.digits, vec![1, 0]);

		let mut a = BigUint::from_limbs(&[0, 0, 1]);
		a.lstrip();
		assert_eq!(a.digits, vec![1]);

		let mut a = BigUint::from_limbs(&[0, 0]);
		a.lstrip();
		assert_eq!(a.digits, vec![0]);

		let mut a = BigUint::from_limbs(&[0, 0, 0]);
		a.lstrip();
		assert_eq!(a.digits, vec![0]);
	}

	#[test]
	fn lpad_works() {
		let mut a = BigUint::from_limbs(&[0, 1, 0]);
		a.lpad(2);
		assert_eq!(a.digits, vec![0, 1, 0]);

		let mut a = BigUint::from_limbs(&[0, 1, 0]);
		a.lpad(3);
		assert_eq!(a.digits, vec![0, 1, 0]);

		let mut a = BigUint::from_limbs(&[0, 1, 0]);
		a.lpad(4);
		assert_eq!(a.digits, vec![0, 0, 1, 0]);
	}

	#[test]
	fn equality_works() {
		assert_eq!(
			BigUint { digits: vec![1, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
			true,
		);
		assert_eq!(
			BigUint { digits: vec![3, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
			false,
		);
		assert_eq!(
			BigUint { digits: vec![0, 1, 2, 3] } == BigUint { digits: vec![1, 2, 3] },
			true,
		);
	}

	#[test]
	fn ordering_works() {
		assert!(BigUint { digits: vec![0] } < BigUint { digits: vec![1] });
		assert!(BigUint { digits: vec![0] } == BigUint { digits: vec![0] });
		assert!(BigUint { digits: vec![] } == BigUint { digits: vec![0] });
		assert!(BigUint { digits: vec![] } == BigUint { digits: vec![] });
		assert!(BigUint { digits: vec![] } < BigUint { digits: vec![1] });

		assert!(BigUint { digits: vec![1, 2, 3] } == BigUint { digits: vec![1, 2, 3] });
		assert!(BigUint { digits: vec![0, 1, 2, 3] } == BigUint { digits: vec![1, 2, 3] });

		assert!(BigUint { digits: vec![1, 2, 4] } > BigUint { digits: vec![1, 2, 3] });
		assert!(BigUint { digits: vec![0, 1, 2, 4] } > BigUint { digits: vec![1, 2, 3] });
		assert!(BigUint { digits: vec![1, 2, 1, 0] } > BigUint { digits: vec![1, 2, 3] });

		assert!(BigUint { digits: vec![0, 1, 2, 1] } < BigUint { digits: vec![1, 2, 3] });
	}

	#[test]
	fn can_try_build_numbers_from_types() {
		use sp_std::convert::TryFrom;
		assert_eq!(u64::try_from(with_limbs(1)).unwrap(), 1);
		assert_eq!(u64::try_from(with_limbs(2)).unwrap(), u32::max_value() as u64 + 2);
		assert_eq!(
			u64::try_from(with_limbs(3)).unwrap_err(),
			"cannot fit a number into u64",
		);
		assert_eq!(
			u128::try_from(with_limbs(3)).unwrap(),
			u32::max_value() as u128 + u64::max_value() as u128 + 3
		);
	}

	#[test]
	fn zero_works() {
		assert_eq!(BigUint::zero(), BigUint { digits: vec![0] });
		assert_eq!(BigUint { digits: vec![0, 1, 0] }.is_zero(), false);
		assert_eq!(BigUint { digits: vec![0, 0, 0] }.is_zero(), true);

		let a = BigUint::zero();
		let b = BigUint::zero();
		let c = a * b;
		assert_eq!(c.digits, vec![0, 0]);
	}

	#[test]
	fn sub_negative_works() {
		assert_eq!(
			BigUint::from(10 as Single).sub(&BigUint::from(5 as Single)).unwrap(),
			BigUint::from(5 as Single)
		);
		assert_eq!(
			BigUint::from(10 as Single).sub(&BigUint::from(10 as Single)).unwrap(),
			BigUint::from(0 as Single)
		);
		assert_eq!(
			BigUint::from(10 as Single).sub(&BigUint::from(13 as Single)).unwrap_err(),
			BigUint::from((B - 3) as Single),
		);
	}

	#[test]
	fn mul_always_appends_one_digit() {
		let a = BigUint::from(10 as Single);
		let b = BigUint::from(4 as Single);
		assert_eq!(a.len(), 1);
		assert_eq!(b.len(), 1);

		let n = a.mul(&b);

		assert_eq!(n.len(), 2);
		assert_eq!(n.digits, vec![0, 40]);
	}

	#[test]
	fn div_conditions_work() {
		let a = BigUint { digits: vec![2] };
		let b = BigUint { digits: vec![1, 2] };
		let c = BigUint { digits: vec![1, 1, 2] };
		let d = BigUint { digits: vec![0, 2] };
		let e = BigUint { digits: vec![0, 1, 1, 2] };
		let f = BigUint { digits: vec![7, 8] };

		assert!(a.clone().div(&b, true).is_none());
		assert!(c.clone().div(&a, true).is_none());
		assert!(c.clone().div(&d, true).is_none());
		assert!(e.clone().div(&a, true).is_none());

		assert!(f.clone().div(&b, true).is_none());
		assert!(c.clone().div(&b, true).is_some());
	}

	#[test]
	fn div_unit_works() {
		let a = BigUint { digits: vec![100] };
		let b = BigUint { digits: vec![1, 100] };
		let c = BigUint { digits: vec![14, 28, 100] };

		assert_eq!(a.clone().div_unit(1), a);
		assert_eq!(a.clone().div_unit(0), a);
		assert_eq!(a.clone().div_unit(2), BigUint::from(50 as Single));
		assert_eq!(a.clone().div_unit(7), BigUint::from(14 as Single));

		assert_eq!(b.clone().div_unit(1), b);
		assert_eq!(b.clone().div_unit(0), b);
		assert_eq!(b.clone().div_unit(2), BigUint::from(((B + 100) / 2) as Single));
		assert_eq!(b.clone().div_unit(7), BigUint::from(((B + 100) / 7) as Single));

		assert_eq!(c.clone().div_unit(1), c);
		assert_eq!(c.clone().div_unit(0), c);
		assert_eq!(c.clone().div_unit(2), BigUint { digits: vec![7, 14, 50] });
		assert_eq!(c.clone().div_unit(7), BigUint { digits: vec![2, 4, 14] });
	}
}
