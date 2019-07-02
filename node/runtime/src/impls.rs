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

//! Some configurable implementations as associated type for the substrate runtime.

use node_primitives::Balance;
use runtime_primitives::weights::{Weight, FeeMultiplier, MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT};
use runtime_primitives::traits::{Convert, Zero};
use crate::{Perbill, Balances};

/// Struct that handles the conversion of Balance -> `u64`. This is used for staking's election
/// calculation.
pub struct CurrencyToVoteHandler;

impl CurrencyToVoteHandler {
	fn factor() -> Balance { (Balances::total_issuance() / u64::max_value() as Balance).max(1) }
}

impl Convert<Balance, u64> for CurrencyToVoteHandler {
	fn convert(x: Balance) -> u64 { (x / Self::factor()) as u64 }
}

impl Convert<u128, Balance> for CurrencyToVoteHandler {
	fn convert(x: u128) -> Balance { x * Self::factor() }
}

/// Struct used to convert from a transaction weight into the actual fee value.
/// This is used in the balances module.
///
/// This assumes that weight is a numeric value in the u32 range.
///
/// Formula:
///   diff = (ideal_weight - current_block_weight)
///   v = 0.00004
///   fee = weight * (1 + (v . diff) + v^2 (v . d)^2 / 2)
///
/// https://research.web3.foundation/en/latest/polkadot/Token%20Economics/#relay-chain-transaction-fees
pub struct FeeMultiplierUpdateHandler;
impl Convert<Weight, FeeMultiplier> for FeeMultiplierUpdateHandler {
	fn convert(block_weight: Weight) -> FeeMultiplier {
		let max_fraction = 1_000_000_000_u128;
		let ideal = IDEAL_TRANSACTIONS_WEIGHT as u128;
		let max = MAX_TRANSACTIONS_WEIGHT as u128;
		let block_weight = block_weight as u128;

		let from_max_to_per_fraction = |x: u128| {
			if let Some(x_fraction) = x.checked_mul(max_fraction) {
				x_fraction / max
			} else {
				max_fraction
			}
		};

		let collapse_mul = |a: u128, b| {
			if let Some(v) = a.checked_mul(b) {
				v
			} else {
				// collapse to zero if it overflow. For now we don't have the accuracy needed to
				// compute this trivially with u128.
				Zero::zero()
			}
		};

		// determines if the first_term is positive
		let positive = block_weight >= ideal;
		let diff = block_weight.max(ideal) - block_weight.min(ideal);

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = 40_000;
		// 0.00004^2 = 16/10^10 ~= 2/10^9
		let v_squared = 2;

		let mut first_term = v;
		first_term = collapse_mul(first_term, from_max_to_per_fraction(diff));
		first_term = first_term / max_fraction;

		// It is very unlikely that this will exist (in our poor perbill estimate) but we are giving
		// it a shot.
		let mut second_term = v_squared;
		second_term = collapse_mul(second_term, from_max_to_per_fraction(diff));
		second_term = collapse_mul(second_term, from_max_to_per_fraction(diff) / 2);
		second_term = second_term / max_fraction;
		second_term = second_term / max_fraction;

		if positive {
			let excess = first_term.saturating_add(second_term);
			// max_fraction is always safe to convert to u32.
			let p = Perbill::from_parts(excess.min(max_fraction) as u32);
			FeeMultiplier::Positive(p)
		} else {
			// first_term > second_term
			let negative = first_term - second_term;
			// max_fraction is always safe to convert to u32.
			let p = Perbill::from_parts(negative.min(max_fraction) as u32);
			FeeMultiplier::Negative(p)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_primitives::weights::{MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT, Weight};

	// poc reference implementation.
	#[allow(dead_code)]
	fn fee_multiplier_update(block_weight: Weight) -> Perbill  {
		let block_weight = block_weight as f32;
		let v: f32 = 0.00004;

		// maximum tx weight
		let m = MAX_TRANSACTIONS_WEIGHT as f32;
		// Ideal saturation in terms of weight
		let ss = IDEAL_TRANSACTIONS_WEIGHT as f32;
		// Current saturation in terms of weight
		let s = block_weight;

		let fm = 1.0 + (v * (s/m - ss/m)) + (v.powi(2) * (s/m - ss/m).powi(2)) / 2.0;
		// return a per-bill-like value.
		let fm = if fm >= 1.0 { fm - 1.0 } else { 1.0 - fm };
		Perbill::from_parts((fm * 1_000_000_000_f32) as u32)
	}

	#[test]
	fn stateless_weight_mul() {
		// Light block. Fee is reduced a little.
		assert_eq!(
			FeeMultiplierUpdateHandler::convert(1024),
			FeeMultiplier::Negative(Perbill::from_parts(9990))
		);
		// a bit more. Fee is decreased less, meaning that the fee increases as the block grows.
		assert_eq!(
			FeeMultiplierUpdateHandler::convert(1024 * 4),
			FeeMultiplier::Negative(Perbill::from_parts(9960))
		);
		// ideal. Original fee.
		assert_eq!(
			FeeMultiplierUpdateHandler::convert(IDEAL_TRANSACTIONS_WEIGHT as u32),
			FeeMultiplier::Positive(Perbill::zero())
		);
		// More than ideal. Fee is increased.
		assert_eq!(
			FeeMultiplierUpdateHandler::convert((IDEAL_TRANSACTIONS_WEIGHT * 2) as u32),
			FeeMultiplier::Positive(Perbill::from_parts(10000))
		);
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		// defensive-only test. at the moment we are not allowing any weight more than 4 * 1024 * 1024
		// in a block.
		let kb = 1024_u32;
		let mb = kb * kb;
		vec![0, 1, 10, 1000, kb, 10 * kb, 100 * kb, mb, 10 * mb, Weight::max_value() / 2, Weight::max_value()]
			.into_iter()
			.for_each(|i| { FeeMultiplierUpdateHandler::convert(i); });
	}
}
