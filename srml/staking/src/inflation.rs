// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! http://research.web3.foundation/en/latest/polkadot/Token%20Economics/#inflation-model

use primitives::{Perbill, traits::SimpleArithmetic};

/// Affine function truncated to positive part `y = max(0, b [+ or -] a*x)` for PNPoS usage
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Affine {
	negative_a: bool,
	// Perbill
	a: u32,
	// Perbill
	b: u32,
}

impl Affine {
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

/// Affine per part function for PNPoS usage
#[derive(Debug, PartialEq, Eq)]
struct AffinePerPart {
	/// Array of tuple of Abscisse in Perbill and Affine.
	///
	/// Each part start with at the abscisse up to the abscisse of the next part.
	parts: [(u32, Affine); 20],
}

impl AffinePerPart {
	fn calculate_for_fraction_times_denominator<N>(&self, n: N, d: N) -> N
	where
		N: SimpleArithmetic + Clone
	{
		let part = self.parts.iter()
			.take_while(|(abscisse, _)| n > Perbill::from_parts(*abscisse) * d.clone())
			.last()
			.unwrap_or(&self.parts[0]);

		part.1.calculate_for_fraction_times_denominator(n, d)
	}
}

// Affine per part approximation of I_NPoS.
const I_NPOS: AffinePerPart = AffinePerPart {
	parts: [
		(0, Affine { negative_a: false, a: 150000000, b: 25000000 }),
		(500000000, Affine { negative_a: true, a: 986493987, b: 593246993 }),
		(507648979, Affine { negative_a: true, a: 884661327, b: 541551747 }),
		(515726279, Affine { negative_a: true, a: 788373842, b: 491893761 }),
		(524282719, Affine { negative_a: true, a: 697631517, b: 444319128 }),
		(533378749, Affine { negative_a: true, a: 612434341, b: 398876765 }),
		(543087019, Affine { negative_a: true, a: 532782338, b: 355618796 }),
		(553495919, Affine { negative_a: true, a: 458675508, b: 314600968 }),
		(564714479, Affine { negative_a: true, a: 390113843, b: 275883203 }),
		(576879339, Affine { negative_a: true, a: 327097341, b: 239530285 }),
		(590164929, Affine { negative_a: true, a: 269626004, b: 205612717 }),
		(604798839, Affine { negative_a: true, a: 217699848, b: 174207838 }),
		(621085859, Affine { negative_a: true, a: 171318873, b: 145401271 }),
		(639447429, Affine { negative_a: true, a: 130483080, b: 119288928 }),
		(660489879, Affine { negative_a: true, a: 95192479, b: 95979842 }),
		(685131379, Affine { negative_a: true, a: 65447076, b: 75600334 }),
		(714860569, Affine { negative_a: true, a: 41246910, b: 58300589 }),
		(752334749, Affine { negative_a: true, a: 22592084, b: 44265915 }),
		(803047659, Affine { negative_a: true, a: 9482996, b: 33738693 }),
		(881691659, Affine { negative_a: true, a: 2572702, b: 27645944 })
	]
};

/// PNPoS: the target total payout to all validators (and their nominators) per era.
///
/// The value take into consideration desired interest rate and inflation rate (see module doc)
/// and is defined as such:
///
/// for x the staking rate in NPoS: `PNPoS(x) = INPoS(x) * current_total_token / era_per_year`
/// i.e.  `PNPoS(x) = INPoS(x) * current_total_token * era_duration / year_duration`
#[allow(unused)]
pub fn compute_total_payout<N>(npos_token_staked: N, total_tokens: N, era_duration: N) -> N
where
	N: SimpleArithmetic + Clone
{
	let year_duration: N = 31_557_600u32.into();
	I_NPOS.calculate_for_fraction_times_denominator(npos_token_staked, total_tokens)
		* era_duration / year_duration
}

#[allow(non_upper_case_globals, non_snake_case)] // To stick with paper notations
#[cfg(test)]
mod test_inflation {
	use std::convert::TryInto;

	// Function `y = a*x + b`
	#[derive(Debug)]
	struct AffineFloat {
		a: f64,
		b: f64,
	}

	impl AffineFloat {
		fn new(x0: f64, y0: f64, x1: f64, y1: f64) -> Self {
			AffineFloat {
				a: (y1 - y0) / (x1 - x0),
				b: (x0*y1 - x1*y0) / (x0 - x1),
			}
		}

		fn compute(&self, x: f64) -> f64 {
			self.a*x + self.b
		}
	}

	#[test]
	fn affine_test() {
		assert_eq!(AffineFloat::new(1.0, 2.0, 4.0, 3.0).compute(7.0), 4.0);
	}

	const I_0: f64 = 0.025;
	const i_ideal: f64 = 0.2;
	const x_ideal: f64 = 0.5;
	const d: f64 = 0.05;

	// Part left to 0.5
	fn I_left(x: f64) -> f64 {
		I_0 + x * (i_ideal - I_0/x_ideal)
	}

	// Part right to 0.5
	fn I_right(x: f64) -> f64 {
		I_0 + (i_ideal*x_ideal - I_0) * 2_f64.powf((x_ideal-x)/d)
	}

	fn I_full(x: f64) -> f64 {
		if x <= 0.5 {
			I_left(x)
		} else {
			I_right(x)
		}
	}

	fn I_NPoS_points() -> super::AffinePerPart {
		let mut points = vec![];

		// Points for left part
		points.push((0.0, I_0));
		points.push((0.5, I_left(0.5)));

		// Approximation for right part
		const STEP_PRECISION: f64 = 0.000_000_1;
		// Max error used for generating points
		const GEN_ERROR: f64 = 0.000_1;

		let mut x0: f64 = 0.5;
		let mut x1: f64 = x0;
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
				let affine = AffineFloat::new(x0, y0, next_x1, next_y1);
				let mut cursor = x0;
				while cursor < x1 {
					if (I_right(cursor) - affine.compute(cursor)).abs() > GEN_ERROR {
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

		let parts: Vec<(u32, super::Affine)> = (0..points.len()-1)
			.map(|i| {
				let p0 = points[i];
				let p1 = points[i+1];

				let affine = AffineFloat::new(p0.0, p0.1, p1.0, p1.1);

				assert!(affine.a.abs() <= 1_000_000_000.0);
				assert!(affine.b.abs() <= 1_000_000_000.0);
				assert!(affine.b.signum() == 1.0);

				(
					(p0.0 * 1_000_000_000.0) as u32,
					super::Affine {
						negative_a: affine.a.signum() < 0.0,
						a: (affine.a.abs() * 1_000_000_000.0) as u32,
						b: (affine.b.abs() * 1_000_000_000.0) as u32,
					}
				)
			})
			.collect();

		println!("Generated parts: {:?}", parts);
		assert_eq!(parts.len(), 20);

		super::AffinePerPart { parts: (&parts[..]).try_into().unwrap() }
	}

	/// This test is only useful to generate a new set of points for the definition of I_NPoS.
	#[test]
	fn generate_I_NPOS() {
		assert_eq!(super::I_NPOS, I_NPoS_points());
	}

	/// This test ensure that i_npos affine per part approximation is close to the actual function.
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
			// TODO TODO: check actually that those values makes sense
		);
	}
}
