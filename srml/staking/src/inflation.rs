// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! This module expose one function `P_NPoS` (Payout NPoS) or `compute_total_payout` which returns
//! the total payout for the era given the era duration and the staking rate in NPoS.
//! The staking rate in NPoS is the total amount of tokens staked by nominators and validators,
//! divided by the total token supply.
//!
//! This payout is computed from the desired yearly inflation `I_NPoS`.
//!
//! `I_NPoS` is defined as such:
//!
//! let's introduce some constant:
//! * `I0` represents a tight upper-bound on our estimate of the operational costs of all
//!    validators, expressed as a fraction of the total token supply. I_NPoS must be always
//!    superior or equal to this value.
//! * `x_ideal` the ideal staking rate in NPoS.
//! * `i_ideal` the ideal yearly interest rate: the ideal total yearly amount of tokens minted to
//!    pay all validators and nominators for NPoS, divided by the total amount of tokens staked by
//!    them. `i(x) = I(x)/x` and `i(x_ideal) = i_deal`
//! * `d` decay rate.
//!
//! We define I_NPoS as a linear function from 0 to `x_ideal` and an exponential decrease after
//! `x_ideal` to 1. We choose exponential decrease for `I_NPoS` because this implies an exponential
//! decrease for the yearly interest rate as well, and we want the interest rate to fall sharply
//! beyond `x_ideal` to avoid illiquidity.
//!
//! Function is defined as such:
//! ```nocompile
//! for 0 < x < x_ideal: I_NPoS(x) = I0 + x*(i_ideal - I0/x_ideal)
//! for x_ideal < x < 1: I_NPoS(x) = I0 + (i_ideal*x_ideal - I0)*2^((x_ideal-x)/d)
//! ```
//!
//! Thus we have the following properties:
//! * `I_NPoS > I0`
//! * `I_NPoS(0) = I0`
//! * `I_NPoS(x_ideal) = max(I_NPoS) = x_ideal*i_ideal`
//! * `i(x)` is monotone decreasing
//!
//! More details can be found [here](http://research.web3.foundation/en/latest/polkadot/Token%20Eco
//! nomics/#inflation-model)


use sr_primitives::{Perbill, traits::SimpleArithmetic};

/// Linear function truncated to positive part `y = max(0, b [+ or -] a*x)` for `P_NPoS` usage.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Linear {
	// Negate the `a*x` term.
	negative_a: bool,
	// Per-billion representation of `a`, the x coefficient.
	a: u32,
	// Per-billion representation of `b`, the intercept.
	b: u32,
}

impl Linear {
	/// Compute `f(n/d)*d`. This is useful to avoid loss of precision.
	fn calculate_for_fraction_times_denominator<N>(&self, n: N, d: N) -> N
	where
		N: SimpleArithmetic + Clone
	{
		if self.negative_a {
			(Perbill::from_parts(self.b) * d).saturating_sub(Perbill::from_parts(self.a) * n)
		} else {
			(Perbill::from_parts(self.b) * d).saturating_add(Perbill::from_parts(self.a) * n)
		}
	}
}

/// Piecewise Linear function for `P_NPoS` usage
#[derive(Debug, PartialEq, Eq)]
struct PiecewiseLinear {
	/// Array of tuples of an abscissa in a per-billion representation and a linear function.
	///
	/// Abscissas in the array must be in order from the lowest to the highest.
	///
	/// The array defines a piecewise linear function as such:
	/// * the n-th segment starts at the abscissa of the n-th element until the abscissa of the
	///     n-th + 1 element, and is defined by the linear function of the n-th element
	/// * last segment doesn't end
	pieces: [(u32, Linear); 20],
}

impl PiecewiseLinear {
	/// Compute `f(n/d)*d`. This is useful to avoid loss of precision.
	fn calculate_for_fraction_times_denominator<N>(&self, n: N, d: N) -> N
	where
		N: SimpleArithmetic + Clone
	{
		let part = self.pieces.iter()
			.take_while(|(abscissa, _)| n > Perbill::from_parts(*abscissa) * d.clone())
			.last()
			.unwrap_or(&self.pieces[0]);

		part.1.calculate_for_fraction_times_denominator(n, d)
	}
}

/// Piecewise linear approximation of `I_NPoS`.
///
/// Using the constants:
/// * `I_0` = 0.025;
/// * `i_ideal` = 0.2;
/// * `x_ideal` = 0.5;
/// * `d` = 0.05;
///
/// This approximation is tested to be close to real one by an error less than 1% see
/// `i_npos_precision` test.
const I_NPOS: PiecewiseLinear = PiecewiseLinear {
	pieces: [
		(0, Linear { negative_a: false, a: 150000000, b: 25000000 }),
		(500000000, Linear { negative_a: true, a: 986493987, b: 593246993 }),
		(507648979, Linear { negative_a: true, a: 884661327, b: 541551747 }),
		(515726279, Linear { negative_a: true, a: 788373842, b: 491893761 }),
		(524282719, Linear { negative_a: true, a: 697631517, b: 444319128 }),
		(533378749, Linear { negative_a: true, a: 612434341, b: 398876765 }),
		(543087019, Linear { negative_a: true, a: 532782338, b: 355618796 }),
		(553495919, Linear { negative_a: true, a: 458675508, b: 314600968 }),
		(564714479, Linear { negative_a: true, a: 390113843, b: 275883203 }),
		(576879339, Linear { negative_a: true, a: 327097341, b: 239530285 }),
		(590164929, Linear { negative_a: true, a: 269626004, b: 205612717 }),
		(604798839, Linear { negative_a: true, a: 217699848, b: 174207838 }),
		(621085859, Linear { negative_a: true, a: 171318873, b: 145401271 }),
		(639447429, Linear { negative_a: true, a: 130483080, b: 119288928 }),
		(660489879, Linear { negative_a: true, a: 95192479, b: 95979842 }),
		(685131379, Linear { negative_a: true, a: 65447076, b: 75600334 }),
		(714860569, Linear { negative_a: true, a: 41246910, b: 58300589 }),
		(752334749, Linear { negative_a: true, a: 22592084, b: 44265915 }),
		(803047659, Linear { negative_a: true, a: 9482996, b: 33738693 }),
		(881691659, Linear { negative_a: true, a: 2572702, b: 27645944 })
	]
};

/// Second per year for the Julian year (365.25 days).
const SECOND_PER_YEAR: u32 = 3600*24*36525/100;

/// The total payout to all validators (and their nominators) per era.
///
/// Named P_NPoS in the [paper](http://research.web3.foundation/en/latest/polkadot/Token%20Ec
/// onomics/#inflation-model).
///
/// For x the staking rate in NPoS: `P_NPoS(x) = I_NPoS(x) * current_total_token / era_per_year`
/// i.e.  `P_NPoS(x) = I_NPoS(x) * current_total_token * era_duration / year_duration`
///
/// I_NPoS is the desired yearly inflation rate for nominated proof of stake.
pub fn compute_total_payout<N>(npos_token_staked: N, total_tokens: N, era_duration: N) -> N
where
	N: SimpleArithmetic + Clone
{
	let year_duration: N = SECOND_PER_YEAR.into();
	I_NPOS.calculate_for_fraction_times_denominator(npos_token_staked, total_tokens)
		* era_duration / year_duration
}

#[allow(non_upper_case_globals, non_snake_case)] // To stick with paper notations
#[cfg(test)]
mod test_inflation {
	use std::convert::TryInto;

	// Function `y = a*x + b` using float used for testing precision of Linear
	#[derive(Debug)]
	struct LinearFloat {
		a: f64,
		b: f64,
	}

	impl LinearFloat {
		fn new(x0: f64, y0: f64, x1: f64, y1: f64) -> Self {
			LinearFloat {
				a: (y1 - y0) / (x1 - x0),
				b: (x0*y1 - x1*y0) / (x0 - x1),
			}
		}

		fn compute(&self, x: f64) -> f64 {
			self.a*x + self.b
		}
	}

	#[test]
	fn linear_float_works() {
		assert_eq!(LinearFloat::new(1.0, 2.0, 4.0, 3.0).compute(7.0), 4.0);
	}

	// Constants defined in paper
	const I_0: f64 = 0.025;
	const i_ideal: f64 = 0.2;
	const x_ideal: f64 = 0.5;
	const d: f64 = 0.05;

	// Left part from `x_ideal`
	fn I_left(x: f64) -> f64 {
		I_0 + x * (i_ideal - I_0/x_ideal)
	}

	// Right part from `x_ideal`
	fn I_right(x: f64) -> f64 {
		I_0 + (i_ideal*x_ideal - I_0) * 2_f64.powf((x_ideal-x)/d)
	}

	// Definition of I_NPoS in float
	fn I_full(x: f64) -> f64 {
		if x <= x_ideal {
			I_left(x)
		} else {
			I_right(x)
		}
	}

	// Compute approximation of I_NPoS into piecewise linear function
	fn I_NPoS_points() -> super::PiecewiseLinear {
		let mut points = vec![];

		// Points for left part
		points.push((0.0, I_0));
		points.push((x_ideal, I_left(x_ideal)));

		// Approximation for right part.
		//
		// We start from x_ideal (x0) and we try to find the next point (x1) for which the linear
		// approximation of (x0, x1) doesn't deviate from float definition by an error of
		// GEN_ERROR.

		// When computing deviation between linear approximation and float definition we iterate
		// over all points with this step precision.
		const STEP_PRECISION: f64 = 0.000_000_1;
		// Max error used for generating points.
		const GEN_ERROR: f64 = 0.000_1;

		let mut x0: f64 = x_ideal;
		let mut x1: f64 = x0;

		// This is just a step used to find next x1:
		// if x1 + step result in a not enought precise approximation we reduce step and try again.
		// we stop as soon as step is less than STEP_PRECISION.
		let mut step: f64 = 0.1;

		loop {
			let next_x1 = x1 + step;

			if next_x1 >= 1.0 {
				points.push((1.0, I_right(1.0)));
				break;
			}

			let y0 = I_right(x0);
			let next_y1 = I_right(next_x1);

			let mut error_overflowed = false;

			// Test error is not overflowed

			// Quick test on one point
			if (I_right((x0 + next_x1)/2.0) - (y0 + next_y1)/2.0).abs() > GEN_ERROR {
				error_overflowed = true;
			}

			// Long test on all points
			if !error_overflowed {
				let linear = LinearFloat::new(x0, y0, next_x1, next_y1);
				let mut cursor = x0;
				while cursor < x1 {
					if (I_right(cursor) - linear.compute(cursor)).abs() > GEN_ERROR {
						error_overflowed = true;
					}
					cursor += STEP_PRECISION;
				}
			}

			if error_overflowed {
				if step <= STEP_PRECISION {
					points.push((x1, I_right(x1)));
					x0 = x1;
					step = 0.1;
				} else {
					step /= 10.0;
				}
			} else {
				x1 = next_x1;
			}
		}

		// Convert points to piecewise linear definition
		let pieces: Vec<(u32, super::Linear)> = (0..points.len()-1)
			.map(|i| {
				let p0 = points[i];
				let p1 = points[i+1];

				let linear = LinearFloat::new(p0.0, p0.1, p1.0, p1.1);

				// Needed if we want to use a Perbill later
				assert!(linear.a.abs() <= 1.0);
				// Needed if we want to use a Perbill later
				assert!(linear.b.abs() <= 1.0);
				// Needed to stick with our restrictive definition of linear
				assert!(linear.b.signum() == 1.0);

				(
					(p0.0 * 1_000_000_000.0) as u32,
					super::Linear {
						negative_a: linear.a.signum() < 0.0,
						a: (linear.a.abs() * 1_000_000_000.0) as u32,
						b: (linear.b.abs() * 1_000_000_000.0) as u32,
					}
				)
			})
			.collect();

		println!("Generated pieces: {:?}", pieces);
		assert_eq!(pieces.len(), 20);

		super::PiecewiseLinear { pieces: (&pieces[..]).try_into().unwrap() }
	}

	/// This test is only useful to generate a new set of points for the definition of I_NPoS.
	#[test]
	fn generate_I_NPOS() {
		assert_eq!(super::I_NPOS, I_NPoS_points());
	}

	/// This test ensure that i_npos piecewise linear approximation is close to the actual function.
	/// It does compare the result from a computation in integer of different capcity and in f64.
	#[test]
	fn i_npos_precision() {
		const STEP_PRECISION: f64 = 0.000_001;
		const ERROR: f64 = 0.000_2;

		macro_rules! test_for_value {
			($($total_token:expr => $type:ty,)*) => {
				let mut x = 0.1;
				while x <= 1.0 {
					let expected = I_full(x);
					$({
						let result = super::I_NPOS.calculate_for_fraction_times_denominator(
							(x * $total_token as f64) as $type,
							$total_token,
						) as f64;
						let expected = expected * $total_token as f64;
						let error = (ERROR * $total_token as f64).max(2.0);

						let diff = (result - expected).abs();
						if diff >= error {
							println!("total_token: {}", $total_token);
							println!("x: {}", x);
							println!("diff: {}", diff);
							println!("error: {}", error);
							panic!("error overflowed");
						}
					})*
					x += STEP_PRECISION
				}
			}
		}

		test_for_value!(
			1_000u32 => u32,
			1_000_000u32 => u32,
			1_000_000_000u32 => u32,
			1_000_000_000_000u64 => u64,
			1_000_000_000_000_000u64 => u64,
			1_000_000_000_000_000_000u64 => u64,
			1_000_000_000_000_000_000_000u128 => u128,
			1_000_000_000_000_000_000_000_000u128 => u128,
			1_000_000_000_000_000_000_000_000_000u128 => u128,
			1_000_000_000_000_000_000_000_000_000_000u128 => u128,
			1_000_000_000_000_000_000_000_000_000_000_000_000u128 => u128,
			u32::max_value() => u32,
			u64::max_value() => u64,
			u128::max_value() => u128,
		);
	}
}
