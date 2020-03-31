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

//! Provides some utilities to define a piecewise linear function.

use crate::{Perbill, traits::{AtLeast32Bit, SaturatedConversion}};
use core::ops::Sub;

/// Piecewise Linear function in [0, 1] -> [0, 1].
#[derive(PartialEq, Eq, sp_core::RuntimeDebug)]
pub struct PiecewiseLinear<'a> {
	/// Array of points. Must be in order from the lowest abscissas to the highest.
	pub points: &'a [(Perbill, Perbill)],
	/// The maximum value that can be returned.
	pub maximum: Perbill,
}

fn abs_sub<N: Ord + Sub<Output=N> + Clone>(a: N, b: N) -> N where {
	a.clone().max(b.clone()) - a.min(b)
}

impl<'a> PiecewiseLinear<'a> {
	/// Compute `f(n/d)*d` with `n <= d`. This is useful to avoid loss of precision.
	pub fn calculate_for_fraction_times_denominator<N>(&self, n: N, d: N) -> N where
		N: AtLeast32Bit + Clone
	{
		let n = n.min(d.clone());

		if self.points.len() == 0 {
			return N::zero()
		}

		let next_point_index = self.points.iter()
			.position(|p| n < p.0 * d.clone());

		let (prev, next) = if let Some(next_point_index) = next_point_index {
			if let Some(previous_point_index) = next_point_index.checked_sub(1) {
				(self.points[previous_point_index], self.points[next_point_index])
			} else {
				// There is no previous points, take first point ordinate
				return self.points.first().map(|p| p.1).unwrap_or_else(Perbill::zero) * d
			}
		} else {
			// There is no next points, take last point ordinate
			return self.points.last().map(|p| p.1).unwrap_or_else(Perbill::zero) * d
		};

		let delta_y = multiply_by_rational_saturating(
			abs_sub(n.clone(), prev.0 * d.clone()),
			abs_sub(next.1.deconstruct(), prev.1.deconstruct()),
			// Must not saturate as prev abscissa > next abscissa
			next.0.deconstruct().saturating_sub(prev.0.deconstruct()),
		);

		// If both subtractions are same sign then result is positive
		if (n > prev.0 * d.clone()) == (next.1.deconstruct() > prev.1.deconstruct()) {
			(prev.1 * d).saturating_add(delta_y)
		// Otherwise result is negative
		} else {
			(prev.1 * d).saturating_sub(delta_y)
		}
	}
}

// Compute value * p / q.
// This is guaranteed not to overflow on whatever values nor lose precision.
// `q` must be superior to zero.
fn multiply_by_rational_saturating<N>(value: N, p: u32, q: u32) -> N
	where N: AtLeast32Bit + Clone
{
	let q = q.max(1);

	// Mul can saturate if p > q
	let result_divisor_part = (value.clone() / q.into()).saturating_mul(p.into());

	let result_remainder_part = {
		let rem = value % q.into();

		// Fits into u32 because q is u32 and remainder < q
		let rem_u32 = rem.saturated_into::<u32>();

		// Multiplication fits into u64 as both term are u32
		let rem_part = rem_u32 as u64 * p as u64 / q as u64;

		// Can saturate if p > q
		rem_part.saturated_into::<N>()
	};

	// Can saturate if p > q
	result_divisor_part.saturating_add(result_remainder_part)
}

#[test]
fn test_multiply_by_rational_saturating() {
	use std::convert::TryInto;

	let div = 100u32;
	for value in 0..=div {
		for p in 0..=div {
			for q in 1..=div {
				let value: u64 = (value as u128 * u64::max_value() as u128 / div as u128)
					.try_into().unwrap();
				let p = (p as u64 * u32::max_value() as u64 / div as u64)
					.try_into().unwrap();
				let q = (q as u64 * u32::max_value() as u64 / div as u64)
					.try_into().unwrap();

				assert_eq!(
					multiply_by_rational_saturating(value, p, q),
					(value as u128 * p as u128 / q as u128)
						.try_into().unwrap_or(u64::max_value())
				);
			}
		}
	}
}

#[test]
fn test_calculate_for_fraction_times_denominator() {
	use std::convert::TryInto;

	let curve = PiecewiseLinear {
		points: &[
			(Perbill::from_parts(0_000_000_000), Perbill::from_parts(0_500_000_000)),
			(Perbill::from_parts(0_500_000_000), Perbill::from_parts(1_000_000_000)),
			(Perbill::from_parts(1_000_000_000), Perbill::from_parts(0_000_000_000)),
		],
		maximum: Perbill::from_parts(1_000_000_000),
	};

	pub fn formal_calculate_for_fraction_times_denominator(n: u64, d: u64) -> u64 {
		if n <= Perbill::from_parts(0_500_000_000) * d.clone() {
			n + d / 2
		} else {
			(d as u128 * 2 - n as u128 * 2).try_into().unwrap()
		}
	}

	let div = 100u32;
	for d in 0..=div {
		for n in 0..=d {
			let d: u64 = (d as u128 * u64::max_value() as u128 / div as u128)
				.try_into().unwrap();
			let n: u64 = (n as u128 * u64::max_value() as u128 / div as u128)
				.try_into().unwrap();

			let res = curve.calculate_for_fraction_times_denominator(n, d);
			let expected = formal_calculate_for_fraction_times_denominator(n, d);

			assert!(abs_sub(res, expected) <= 1);
		}
	}
}
