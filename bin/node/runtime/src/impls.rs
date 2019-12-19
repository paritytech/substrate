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
use sp_runtime::traits::{Convert, Saturating};
use sp_runtime::{Fixed64, Perbill};
use frame_support::{traits::{OnUnbalanced, Currency, Get}, weights::Weight};
use crate::{Balances, System, Authorship, MaximumBlockWeight, NegativeImbalance};

pub struct Author;
impl OnUnbalanced<NegativeImbalance> for Author {
	fn on_nonzero_unbalanced(amount: NegativeImbalance) {
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

/// Convert from weight to balance via a simple coefficient multiplication
/// The associated type C encapsulates a constant in units of balance per weight
pub struct LinearWeightToFee<C>(sp_std::marker::PhantomData<C>);

impl<C: Get<Balance>> Convert<Weight, Balance> for LinearWeightToFee<C> {
	fn convert(w: Weight) -> Balance {
		// substrate-node a weight of 10_000 (smallest non-zero weight) to be mapped to 10^7 units of
		// fees, hence:
		let coefficient = C::get();
		Balance::from(w).saturating_mul(coefficient)
	}
}

/// Update the given multiplier based on the following formula
///
///   diff = (previous_block_weight - target_weight)
///   v = 0.00004
///   next_weight = weight * (1 + (v . diff) + (v . diff)^2 / 2)
///
/// Where `target_weight` must be given as the `Get` implementation of the `T` generic type.
/// https://research.web3.foundation/en/latest/polkadot/Token%20Economics/#relay-chain-transaction-fees
pub struct TargetedFeeAdjustment<T>(sp_std::marker::PhantomData<T>);

impl<T: Get<Perbill>> Convert<Fixed64, Fixed64> for TargetedFeeAdjustment<T> {
	fn convert(multiplier: Fixed64) -> Fixed64 {
		let block_weight = System::all_extrinsics_weight();
		let max_weight = MaximumBlockWeight::get();
		let target_weight = (T::get() * max_weight) as u128;
		let block_weight = block_weight as u128;

		// determines if the first_term is positive
		let positive = block_weight >= target_weight;
		let diff_abs = block_weight.max(target_weight) - block_weight.min(target_weight);
		// diff is within u32, safe.
		let diff = Fixed64::from_rational(diff_abs as i64, max_weight as u64);
		let diff_squared = diff.saturating_mul(diff);

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = Fixed64::from_rational(4, 100_000);
		// 0.00004^2 = 16/10^10 ~= 2/10^9. Taking the future /2 into account, then it is just 1
		// parts from a billionth.
		let v_squared_2 = Fixed64::from_rational(1, 1_000_000_000);

		let first_term = v.saturating_mul(diff);
		// It is very unlikely that this will exist (in our poor perbill estimate) but we are giving
		// it a shot.
		let second_term = v_squared_2.saturating_mul(diff_squared);

		if positive {
			// Note: this is merely bounded by how big the multiplier and the inner value can go,
			// not by any economical reasoning.
			let excess = first_term.saturating_add(second_term);
			multiplier.saturating_add(excess)
		} else {
			// Proof: first_term > second_term. Safe subtraction.
			let negative = first_term - second_term;
			multiplier.saturating_sub(negative)
				// despite the fact that apply_to saturates weight (final fee cannot go below 0)
				// it is crucially important to stop here and don't further reduce the weight fee
				// multiplier. While at -1, it means that the network is so un-congested that all
				// transactions have no weight fee. We stop here and only increase if the network
				// became more busy.
				.max(Fixed64::from_rational(-1, 1))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::assert_eq_error_rate;
	use crate::{MaximumBlockWeight, AvailableBlockRatio, Runtime};
	use crate::{constants::currency::*, TransactionPayment, TargetBlockFullness};
	use frame_support::weights::Weight;

	fn max() -> Weight {
		MaximumBlockWeight::get()
	}

	fn target() -> Weight {
		TargetBlockFullness::get() * max()
	}

	// poc reference implementation.
	fn fee_multiplier_update(block_weight: Weight, previous: Fixed64) -> Fixed64  {
		let block_weight = block_weight as f32;
		let v: f32 = 0.00004;

		// maximum tx weight
		let m = max() as f32;
		// Ideal saturation in terms of weight
		let ss = target() as f32;
		// Current saturation in terms of weight
		let s = block_weight;

		let fm = v * (s/m - ss/m) + v.powi(2) * (s/m - ss/m).powi(2) / 2.0;
		let addition_fm = Fixed64::from_parts((fm * 1_000_000_000_f32).round() as i64);
		previous.saturating_add(addition_fm)
	}

	fn feemul(parts: i64) -> Fixed64 {
		Fixed64::from_parts(parts)
	}

	fn run_with_system_weight<F>(w: Weight, assertions: F) where F: Fn() -> () {
		let mut t: sp_io::TestExternalities =
			frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap().into();
		t.execute_with(|| {
			System::set_block_limits(w, 0);
			assertions()
		});
	}

	#[test]
	fn fee_multiplier_update_poc_works() {
		let fm = Fixed64::from_rational(0, 1);
		let test_set = vec![
			(0, fm.clone()),
			(100, fm.clone()),
			(target(), fm.clone()),
			(max() / 2, fm.clone()),
			(max(), fm.clone()),
		];
		test_set.into_iter().for_each(|(w, fm)| {
			run_with_system_weight(w, || {
				assert_eq_error_rate!(
					fee_multiplier_update(w, fm).into_inner(),
					TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm).into_inner(),
					5,
				);
			})
		})
	}

	#[test]
	fn empty_chain_simulation() {
		// just a few txs per_block.
		let block_weight = 0;
		run_with_system_weight(block_weight, || {
			let mut fm = Fixed64::default();
			let mut iterations: u64 = 0;
			loop {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm);
				fm = next;
				if fm == Fixed64::from_rational(-1, 1) { break; }
				iterations += 1;
			}
			println!("iteration {}, new fm = {:?}. Weight fee is now zero", iterations, fm);
			assert!(iterations > 50_000, "This assertion is just a warning; Don't panic. \
				Current substrate/polkadot node are configured with a _slow adjusting fee_ \
				mechanism. Hence, it is really unlikely that fees collapse to zero even on an \
				empty chain in less than at least of couple of thousands of empty blocks. But this \
				simulation indicates that fees collapsed to zero after {} almost-empty blocks. \
				Check it",
				iterations,
			);
		})
	}

	#[test]
	#[ignore]
	fn congested_chain_simulation() {
		// `cargo test congested_chain_simulation -- --nocapture` to get some insight.

		// almost full. The entire quota of normal transactions is taken.
		let block_weight = AvailableBlockRatio::get() * max() - 100;

		// Default substrate minimum.
		let tx_weight = 10_000;

		run_with_system_weight(block_weight, || {
			// initial value configured on module
			let mut fm = Fixed64::default();
			assert_eq!(fm, TransactionPayment::next_fee_multiplier());

			let mut iterations: u64 = 0;
			loop {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm);
				// if no change, panic. This should never happen in this case.
				if fm == next { panic!("The fee should ever increase"); }
				fm = next;
				iterations += 1;
				let fee = <Runtime as pallet_transaction_payment::Trait>::WeightToFee::convert(tx_weight);
				let adjusted_fee = fm.saturated_multiply_accumulate(fee);
				println!(
					"iteration {}, new fm = {:?}. Fee at this point is: {} units / {} millicents, \
					{} cents, {} dollars",
					iterations,
					fm,
					adjusted_fee,
					adjusted_fee / MILLICENTS,
					adjusted_fee / CENTS,
					adjusted_fee / DOLLARS,
				);
			}
		});
	}

	#[test]
	fn stateless_weight_mul() {
		run_with_system_weight(target() / 4, || {
			// Light block. Fee is reduced a little.
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(-7500),
			);
		});
		run_with_system_weight(target() / 2, || {
			// a bit more. Fee is decreased less, meaning that the fee increases as the block grows.
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(-5000),
			);

		});
		run_with_system_weight(target(), || {
			// ideal. Original fee. No changes.
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(0),
			);
		});
		run_with_system_weight(target() * 2, || {
			// // More than ideal. Fee is increased.
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(10000),
			);
		});
	}

	#[test]
	fn stateful_weight_mul_grow_to_infinity() {
		run_with_system_weight(target() * 2, || {
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(10000)
			);
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(10000)),
				feemul(20000)
			);
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(20000)),
				feemul(30000)
			);
			// ...
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(1_000_000_000)),
				feemul(1_000_000_000 + 10000)
			);
		});
	}

	#[test]
	fn stateful_weight_mil_collapse_to_minus_one() {
		run_with_system_weight(0, || {
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default()),
				feemul(-10000)
			);
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(-10000)),
				feemul(-20000)
			);
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(-20000)),
				feemul(-30000)
			);
			// ...
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(feemul(1_000_000_000 * -1)),
				feemul(-1_000_000_000)
			);
		})
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		let kb = 1024 as Weight;
		let mb = kb * kb;
		let max_fm = Fixed64::from_natural(i64::max_value());

		// check that for all values it can compute, correctly.
		vec![
			0,
			1,
			10,
			1000,
			kb,
			10 * kb,
			100 * kb,
			mb,
			10 * mb,
			Weight::max_value() / 2,
			Weight::max_value(),
		].into_iter().for_each(|i| {
			run_with_system_weight(i, || {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Fixed64::default());
				let truth = fee_multiplier_update(i, Fixed64::default());
				assert_eq_error_rate!(truth.into_inner(), next.into_inner(), 5);
			});
		});

		// Some values that are all above the target and will cause an increase.
		let t = target();
		vec![t + 100, t * 2, t * 4]
			.into_iter()
			.for_each(|i| {
				run_with_system_weight(i, || {
					let fm = TargetedFeeAdjustment::<TargetBlockFullness>::convert(max_fm);
					// won't grow. The convert saturates everything.
					assert_eq!(fm, max_fm);
				})
			});
	}
}
