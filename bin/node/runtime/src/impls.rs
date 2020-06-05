// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Some configurable implementations as associated type for the substrate runtime.

use node_primitives::Balance;
use sp_runtime::traits::{Convert, Saturating};
use sp_runtime::{FixedPointNumber, Perquintill};
use frame_support::traits::{OnUnbalanced, Currency, Get};
use pallet_transaction_payment::Multiplier;
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

/// Update the given multiplier based on the following formula
///
///   diff = (previous_block_weight - target_weight)/max_weight
///   v = 0.00004
///   next_weight = weight * (1 + (v * diff) + (v * diff)^2 / 2)
///
/// Where `target_weight` must be given as the `Get` implementation of the `T` generic type.
/// https://research.web3.foundation/en/latest/polkadot/Token%20Economics/#relay-chain-transaction-fees
pub struct TargetedFeeAdjustment<T>(sp_std::marker::PhantomData<T>);

impl<T: Get<Perquintill>> Convert<Multiplier, Multiplier> for TargetedFeeAdjustment<T> {
	fn convert(multiplier: Multiplier) -> Multiplier {
		let max_weight = MaximumBlockWeight::get();
		let block_weight = System::block_weight().total().min(max_weight);
		let target_weight = (T::get() * max_weight) as u128;
		let block_weight = block_weight as u128;

		// determines if the first_term is positive
		let positive = block_weight >= target_weight;
		let diff_abs = block_weight.max(target_weight) - block_weight.min(target_weight);
		// safe, diff_abs cannot exceed u64.
		let diff = Multiplier::saturating_from_rational(diff_abs, max_weight.max(1));
		let diff_squared = diff.saturating_mul(diff);

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = Multiplier::saturating_from_rational(4, 100_000);
		// 0.00004^2 = 16/10^10 Taking the future /2 into account... 8/10^10
		let v_squared_2 = Multiplier::saturating_from_rational(8, 10_000_000_000u64);

		let first_term = v.saturating_mul(diff);
		let second_term = v_squared_2.saturating_mul(diff_squared);

		if positive {
			// Note: this is merely bounded by how big the multiplier and the inner value can go,
			// not by any economical reasoning.
			let excess = first_term.saturating_add(second_term);
			multiplier.saturating_add(excess)
		} else {
			// Defensive-only: first_term > second_term. Safe subtraction.
			let negative = first_term.saturating_sub(second_term);
			multiplier.saturating_sub(negative)
				// despite the fact that apply_to saturates weight (final fee cannot go below 0)
				// it is crucially important to stop here and don't further reduce the weight fee
				// multiplier. While at -1, it means that the network is so un-congested that all
				// transactions have no weight fee. We stop here and only increase if the network
				// became more busy.
				.max(Multiplier::saturating_from_integer(-1))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::assert_eq_error_rate;
	use crate::{MaximumBlockWeight, AvailableBlockRatio, Runtime};
	use crate::{constants::currency::*, TransactionPayment, TargetBlockFullness};
	use frame_support::weights::{Weight, WeightToFeePolynomial};

	fn max() -> Weight {
		MaximumBlockWeight::get()
	}

	fn target() -> Weight {
		TargetBlockFullness::get() * max()
	}

	// poc reference implementation.
	fn fee_multiplier_update(block_weight: Weight, previous: Multiplier) -> Multiplier  {
		// maximum tx weight
		let m = max() as f64;
		// block weight always truncated to max weight
		let block_weight = (block_weight as f64).min(m);
		let v: f64 = 0.00004;

		// Ideal saturation in terms of weight
		let ss = target() as f64;
		// Current saturation in terms of weight
		let s = block_weight;

		let fm = v * (s/m - ss/m) + v.powi(2) * (s/m - ss/m).powi(2) / 2.0;
		let addition_fm = Multiplier::from_inner((fm * Multiplier::accuracy() as f64).round() as i128);
		previous.saturating_add(addition_fm)
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
		let fm = Multiplier::saturating_from_rational(0, 1);
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
					fee_multiplier_update(w, fm),
					TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm),
					// Error is only 1 in 10^18
					Multiplier::from_inner(1),
				);
			})
		})
	}

	#[test]
	fn empty_chain_simulation() {
		// just a few txs per_block.
		let block_weight = 0;
		run_with_system_weight(block_weight, || {
			let mut fm = Multiplier::default();
			let mut iterations: u64 = 0;
			loop {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm);
				fm = next;
				if fm == Multiplier::saturating_from_integer(-1) { break; }
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
			let mut fm = Multiplier::default();
			assert_eq!(fm, TransactionPayment::next_fee_multiplier());

			let mut iterations: u64 = 0;
			loop {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(fm);
				// if no change, panic. This should never happen in this case.
				if fm == next { panic!("The fee should ever increase"); }
				fm = next;
				iterations += 1;
				let fee =
					<Runtime as pallet_transaction_payment::Trait>::WeightToFee::calc(&tx_weight);
				let adjusted_fee = fm.saturating_mul_acc_int(fee);
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
		// This test will show that heavy blocks have a weight multiplier greater than 0
		// and light blocks will have a weight multiplier less than 0.
		run_with_system_weight(target() / 4, || {
			// `fee_multiplier_update` is enough as it is the absolute truth value.
			let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::default());
			assert_eq!(
				next,
				fee_multiplier_update(target() / 4 ,Multiplier::default())
			);

			// Light block. Fee is reduced a little.
			assert!(next < Multiplier::zero())
		});
		run_with_system_weight(target() / 2, || {
			let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::default());
			assert_eq!(
				next,
				fee_multiplier_update(target() / 2 ,Multiplier::default())
			);

			// Light block. Fee is reduced a little.
			assert!(next < Multiplier::zero())

		});
		run_with_system_weight(target(), || {
			// ideal. Original fee. No changes.
			let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::default());
			assert_eq!(next, Multiplier::zero())
		});
		run_with_system_weight(target() * 2, || {
			// More than ideal. Fee is increased.
			let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::default());
			assert_eq!(
				next,
				fee_multiplier_update(target() * 2 ,Multiplier::default())
			);

			// Heavy block. Fee is increased a little.
			assert!(next > Multiplier::zero())
		});
	}

	#[test]
	fn stateful_weight_mul_grow_to_infinity() {
		run_with_system_weight(target() * 2, || {
			let mut original = Multiplier::default();
			let mut next = Multiplier::default();

			(0..1_000).for_each(|_| {
				next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(original);
				assert_eq!(
					next,
					fee_multiplier_update(target() * 2, original),
				);
				// must always increase
				assert!(next > original);
				original = next;
			});
		});
	}

	#[test]
	fn stateful_weight_mil_collapse_to_minus_one() {
		run_with_system_weight(0, || {
			let mut original = Multiplier::default(); // 0
			let mut next;

			// decreases
			next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(original);
			assert_eq!(
				next,
				fee_multiplier_update(0, original),
			);
			assert!(next < original);
			original = next;

			// keeps decreasing
			next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(original);
			assert_eq!(
				next,
				fee_multiplier_update(0, original),
			);
			assert!(next < original);

			// ... stops going down at -1
			assert_eq!(
				TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::saturating_from_integer(-1)),
				Multiplier::saturating_from_integer(-1)
			);
		})
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		let kb = 1024 as Weight;
		let mb = kb * kb;
		let max_fm = Multiplier::saturating_from_integer(i128::max_value());

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
			2147483647,
			4294967295,
			MaximumBlockWeight::get() / 2,
			MaximumBlockWeight::get(),
			Weight::max_value() / 2,
			Weight::max_value(),
		].into_iter().for_each(|i| {
			run_with_system_weight(i, || {
				let next = TargetedFeeAdjustment::<TargetBlockFullness>::convert(Multiplier::default());
				let truth = fee_multiplier_update(i, Multiplier::default());
				assert_eq_error_rate!(truth, next, Multiplier::from_inner(50_000_000));
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
