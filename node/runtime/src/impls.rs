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
use runtime_primitives::weights::{Weight, WeightMultiplier};
use runtime_primitives::traits::{Convert, Saturating};
use runtime_primitives::Fixed64;
use support::traits::Get;
use crate::{Balances, MaximumBlockWeight};

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

/// A struct that updates the weight multiplier based on the saturation level of the previous block.
/// This should typically be called once per-block.
///
/// This assumes that weight is a numeric value in the u32 range.
///
/// Formula:
///   diff = (ideal_weight - current_block_weight)
///   v = 0.00004
///   next_weight = weight * (1 + (v . diff) + (v . diff)^2 / 2)
///
/// https://research.web3.foundation/en/latest/polkadot/Token%20Economics/#relay-chain-transaction-fees
pub struct WeightMultiplierUpdateHandler;
impl Convert<(Weight, WeightMultiplier), WeightMultiplier> for WeightMultiplierUpdateHandler {
	fn convert(previous_state: (Weight, WeightMultiplier)) -> WeightMultiplier {
		let (block_weight, multiplier) = previous_state;
		// CRITICAL NOTE: what the system module interprets as maximum block weight, and a portion
		// of it (1/4 usually) as ideal weight demonstrate the gap in block weights for operational
		// transactions. What this weight multiplier interprets as the maximum, is actually the
		// maximum that is available to normal transactions. Hence,
		let max_weight = <MaximumBlockWeight as Get<u32>>::get() / 4;
		let ideal_weight = (max_weight / 4) as u128;
		let block_weight = block_weight as u128;

		// determines if the first_term is positive
		let positive = block_weight >= ideal_weight;
		let diff_abs = block_weight.max(ideal_weight) - block_weight.min(ideal_weight);
		// diff is within u32, safe.
		let diff = Fixed64::from_rational(diff_abs as i64, max_weight as u64);
		let diff_squared = diff.saturating_mul(diff);

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = Fixed64::from_rational(4, 100_000);
		// 0.00004^2 = 16/10^10 ~= 2/10^9. Taking the future /2 into account, then it is just 1 parts
		// from a billionth.
		let v_squared_2 = Fixed64::from_rational(1, 1_000_000_000);

		let first_term = v.saturating_mul(diff);
		// It is very unlikely that this will exist (in our poor perbill estimate) but we are giving
		// it a shot.
		let second_term = v_squared_2.saturating_mul(diff_squared);

		if positive {
			let excess = first_term.saturating_add(second_term);
			multiplier.saturating_add(WeightMultiplier::from_fixed(excess))
		} else {
			// first_term > second_term
			let negative = first_term - second_term;
			multiplier.saturating_sub(WeightMultiplier::from_fixed(negative))
				// despite the fact that apply_to saturates weight (final fee cannot go below 0)
				// it is crucially important to stop here and don't further reduce the weight fee
				// multiplier. While at -1, it means that the network is so un-congested that all
				// transactions are practically free. We stop here and only increase if the network
				// became more busy.
				.max(WeightMultiplier::from_rational(-1, 1))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_primitives::weights::Weight;
	use runtime_primitives::Perbill;

	fn max() -> Weight {
		<MaximumBlockWeight as Get<Weight>>::get()
	}

	fn ideal() -> Weight {
		max() / 4 / 4
	}

	// poc reference implementation.
	#[allow(dead_code)]
	fn weight_multiplier_update(block_weight: Weight) -> Perbill  {
		let block_weight = block_weight as f32;
		let v: f32 = 0.00004;

		// maximum tx weight
		let m = max() as f32;
		// Ideal saturation in terms of weight
		let ss = ideal() as f32;
		// Current saturation in terms of weight
		let s = block_weight;

		let fm = 1.0 + (v * (s/m - ss/m)) + (v.powi(2) * (s/m - ss/m).powi(2)) / 2.0;
		// return a per-bill-like value.
		let fm = if fm >= 1.0 { fm - 1.0 } else { 1.0 - fm };
		Perbill::from_parts((fm * 1_000_000_000_f32) as u32)
	}

	fn fm(parts: i64) -> WeightMultiplier {
		WeightMultiplier::from_parts(parts)
	}

	#[test]
	fn stateless_weight_mul() {
		// Light block. Fee is reduced a little.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() / 4, WeightMultiplier::default())),
			fm(-7500)
		);
		// a bit more. Fee is decreased less, meaning that the fee increases as the block grows.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() / 2, WeightMultiplier::default())),
			fm(-5000)
		);
		// ideal. Original fee. No changes.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() as u32, WeightMultiplier::default())),
			fm(0)
		);
		// // More than ideal. Fee is increased.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert(((ideal() * 2) as u32, WeightMultiplier::default())),
			fm(10000)
		);
	}

	#[test]
	fn stateful_weight_mul_grow_to_infinity() {
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() * 2, WeightMultiplier::default())),
			fm(10000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() * 2, fm(10000))),
			fm(20000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() * 2, fm(20000))),
			fm(30000)
		);
		// ...
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((ideal() * 2, fm(1_000_000_000))),
			fm(1_000_000_000 + 10000)
		);
	}

	#[test]
	fn stateful_weight_mil_collapse_to_minus_one() {
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, WeightMultiplier::default())),
			fm(-10000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, fm(-10000))),
			fm(-20000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, fm(-20000))),
			fm(-30000)
		);
		// ...
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, fm(1_000_000_000 * -1))),
			fm(-1_000_000_000)
		);
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		// defensive-only test. at the moment we are not allowing any weight more than
		// 4 * 1024 * 1024 in a block.
		let kb = 1024_u32;
		let mb = kb * kb;
		let max_fm = WeightMultiplier::from_fixed(Fixed64::from_natural(i64::max_value()));

		vec![0, 1, 10, 1000, kb, 10 * kb, 100 * kb, mb, 10 * mb, Weight::max_value() / 2, Weight::max_value()]
			.into_iter()
			.for_each(|i| {
				WeightMultiplierUpdateHandler::convert((i, WeightMultiplier::default()));
			});

		vec![10 * mb, Weight::max_value() / 2, Weight::max_value()]
			.into_iter()
			.for_each(|i| {
				let fm = WeightMultiplierUpdateHandler::convert((
					i,
					max_fm
				));
				// won't grow. The convert saturates everything.
				assert_eq!(fm, max_fm);
			});
	}
}
