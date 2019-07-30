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
use sr_primitives::weights::{Weight, WeightMultiplier};
use sr_primitives::traits::{Convert, Saturating};
use sr_primitives::Fixed64;
use support::traits::{OnUnbalanced, Currency};
use crate::{Balances, Authorship, MaximumBlockWeight, NegativeImbalance};
use crate::constants::fee::TARGET_BLOCK_FULLNESS;

pub struct Author;
impl OnUnbalanced<NegativeImbalance> for Author {
	fn on_unbalanced(amount: NegativeImbalance) {
		Balances::resolve_creating(&Authorship::author(), amount);
	}
}

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

/// Handles converting a weight scalar to a fee value, based on the scale and granularity of the
/// node's balance type.
///
/// This should typically create a mapping between the following ranges:
///   - [0, system::MaximumBlockWeight]
///   - [Balance::min, Balance::max]
///
/// Yet, it can be used for any other sort of change to weight-fee. Some examples being:
///   - Setting it to `0` will essentially disable the weight fee.
///   - Setting it to `1` will cause the literal `#[weight = x]` values to be charged.
///
/// By default, substrate node will have a weight range of [0, 1_000_000_000].
pub struct WeightToFee;
impl Convert<Weight, Balance> for WeightToFee {
	fn convert(x: Weight) -> Balance {
		// substrate-node a weight of 10_000 (smallest non-zero weight) to be mapped to 10^7 units of
		// fees, hence:
		Balance::from(x).saturating_mul(1_000)
	}
}

/// A struct that updates the weight multiplier based on the saturation level of the previous block.
/// This should typically be called once per-block.
///
/// This assumes that weight is a numeric value in the u32 range.
///
/// Given `TARGET_BLOCK_FULLNESS = 1/2`, a block saturation greater than 1/2 will cause the system
/// fees to slightly grow and the opposite for block saturations less than 1/2.
///
/// Formula:
///   diff = (target_weight - current_block_weight)
///   v = 0.00004
///   next_weight = weight * (1 + (v . diff) + (v . diff)^2 / 2)
///
/// https://research.web3.foundation/en/latest/polkadot/Token%20Economics/#relay-chain-transaction-fees
pub struct WeightMultiplierUpdateHandler;

impl Convert<(Weight, WeightMultiplier), WeightMultiplier> for WeightMultiplierUpdateHandler {
	fn convert(previous_state: (Weight, WeightMultiplier)) -> WeightMultiplier {
		let (block_weight, multiplier) = previous_state;
		let max_weight = MaximumBlockWeight::get();
		let target_weight = (TARGET_BLOCK_FULLNESS * max_weight) as u128;
		let block_weight = block_weight as u128;

		// determines if the first_term is positive
		let positive = block_weight >= target_weight;
		let diff_abs = block_weight.max(target_weight) - block_weight.min(target_weight);
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
			// Note: this is merely bounded by how big the multiplier and the inner value can go,
			// not by any economical reasoning.
			let excess = first_term.saturating_add(second_term);
			multiplier.saturating_add(WeightMultiplier::from_fixed(excess))
		} else {
			// first_term > second_term
			let negative = first_term - second_term;
			multiplier.saturating_sub(WeightMultiplier::from_fixed(negative))
				// despite the fact that apply_to saturates weight (final fee cannot go below 0)
				// it is crucially important to stop here and don't further reduce the weight fee
				// multiplier. While at -1, it means that the network is so un-congested that all
				// transactions have no weight fee. We stop here and only increase if the network
				// became more busy.
				.max(WeightMultiplier::from_rational(-1, 1))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sr_primitives::weights::Weight;
	use sr_primitives::Perbill;
	use crate::{MaximumBlockWeight, AvailableBlockRatio, Runtime};
	use crate::constants::currency::*;

	fn max() -> Weight {
		MaximumBlockWeight::get()
	}

	fn target() -> Weight {
		TARGET_BLOCK_FULLNESS * max()
	}

	// poc reference implementation.
	#[allow(dead_code)]
	fn weight_multiplier_update(block_weight: Weight) -> Perbill  {
		let block_weight = block_weight as f32;
		let v: f32 = 0.00004;

		// maximum tx weight
		let m = max() as f32;
		// Ideal saturation in terms of weight
		let ss = target() as f32;
		// Current saturation in terms of weight
		let s = block_weight;

		let fm = 1.0 + (v * (s/m - ss/m)) + (v.powi(2) * (s/m - ss/m).powi(2)) / 2.0;
		// return a per-bill-like value.
		let fm = if fm >= 1.0 { fm - 1.0 } else { 1.0 - fm };
		Perbill::from_parts((fm * 1_000_000_000_f32) as u32)
	}

	fn wm(parts: i64) -> WeightMultiplier {
		WeightMultiplier::from_parts(parts)
	}

	#[test]
	fn empty_chain_simulation() {
		// just a few txs per_block.
		let block_weight = 1000;
		let mut wm = WeightMultiplier::default();
		let mut iterations: u64 = 0;
		loop {
			let next = WeightMultiplierUpdateHandler::convert((block_weight, wm));
			wm = next;
			if wm == WeightMultiplier::from_rational(-1, 1) { break; }
			iterations += 1;
		}
		println!("iteration {}, new wm = {:?}. Weight fee is now zero", iterations, wm);
	}

	#[test]
	#[ignore]
	fn congested_chain_simulation() {
		// `cargo test congested_chain_simulation -- --nocapture` to get some insight.
		// almost full. The entire quota of normal transactions is taken.
		let block_weight = AvailableBlockRatio::get() * max();
		let tx_weight = 1000;
		let mut wm = WeightMultiplier::default();
		let mut iterations: u64 = 0;
		loop {
			let next = WeightMultiplierUpdateHandler::convert((block_weight, wm));
			if wm == next { break; }
			wm = next;
			iterations += 1;
			let fee = <Runtime as balances::Trait>::WeightToFee::convert(wm.apply_to(tx_weight));
			println!(
				"iteration {}, new wm = {:?}. Fee at this point is: {} millicents, {} cents, {} dollars",
				iterations,
				wm,
				fee / MILLICENTS,
				fee / CENTS,
				fee / DOLLARS
			);
		}
	}

	#[test]
	fn stateless_weight_mul() {
		// Light block. Fee is reduced a little.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() / 4, WeightMultiplier::default())),
			wm(-7500)
		);
		// a bit more. Fee is decreased less, meaning that the fee increases as the block grows.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() / 2, WeightMultiplier::default())),
			wm(-5000)
		);
		// ideal. Original fee. No changes.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target(), WeightMultiplier::default())),
			wm(0)
		);
		// // More than ideal. Fee is increased.
		assert_eq!(
			WeightMultiplierUpdateHandler::convert(((target() * 2), WeightMultiplier::default())),
			wm(10000)
		);
	}

	#[test]
	fn stateful_weight_mul_grow_to_infinity() {
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() * 2, WeightMultiplier::default())),
			wm(10000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() * 2, wm(10000))),
			wm(20000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() * 2, wm(20000))),
			wm(30000)
		);
		// ...
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((target() * 2, wm(1_000_000_000))),
			wm(1_000_000_000 + 10000)
		);
	}

	#[test]
	fn stateful_weight_mil_collapse_to_minus_one() {
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, WeightMultiplier::default())),
			wm(-10000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, wm(-10000))),
			wm(-20000)
		);
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, wm(-20000))),
			wm(-30000)
		);
		// ...
		assert_eq!(
			WeightMultiplierUpdateHandler::convert((0, wm(1_000_000_000 * -1))),
			wm(-1_000_000_000)
		);
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		let kb = 1024 as Weight;
		let mb = kb * kb;
		let max_fm = WeightMultiplier::from_fixed(Fixed64::from_natural(i64::max_value()));

		vec![0, 1, 10, 1000, kb, 10 * kb, 100 * kb, mb, 10 * mb, Weight::max_value() / 2, Weight::max_value()]
			.into_iter()
			.for_each(|i| {
				WeightMultiplierUpdateHandler::convert((i, WeightMultiplier::default()));
			});

		// Some values that are all above the target and will cause an increase.
		let t = target();
		vec![t + 100, t * 2, t * 4]
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
