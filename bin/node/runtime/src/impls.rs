// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use frame_support::{
	pallet_prelude::*,
	traits::{
		fungibles::{Balanced, Credit},
		Currency, OnUnbalanced,
	},
};
use pallet_alliance::{IdentityVerifier, ProposalIndex, ProposalProvider};
use pallet_asset_tx_payment::HandleCredit;
use sp_std::prelude::*;

use crate::{
	AccountId, AllianceMotion, Assets, Authorship, Balances, Hash, NegativeImbalance, Runtime,
	RuntimeCall,
};

pub struct Author;
impl OnUnbalanced<NegativeImbalance> for Author {
	fn on_nonzero_unbalanced(amount: NegativeImbalance) {
		if let Some(author) = Authorship::author() {
			Balances::resolve_creating(&author, amount);
		}
	}
}

/// A `HandleCredit` implementation that naively transfers the fees to the block author.
/// Will drop and burn the assets in case the transfer fails.
pub struct CreditToBlockAuthor;
impl HandleCredit<AccountId, Assets> for CreditToBlockAuthor {
	fn handle_credit(credit: Credit<AccountId, Assets>) {
		if let Some(author) = pallet_authorship::Pallet::<Runtime>::author() {
			// Drop the result which will trigger the `OnDrop` of the imbalance in case of error.
			let _ = Assets::resolve(&author, credit);
		}
	}
}

pub struct AllianceIdentityVerifier;
impl IdentityVerifier<AccountId> for AllianceIdentityVerifier {
	fn has_identity(who: &AccountId, fields: u64) -> bool {
		crate::Identity::has_identity(who, fields)
	}

	fn has_good_judgement(who: &AccountId) -> bool {
		use pallet_identity::Judgement;
		crate::Identity::identity(who)
			.map(|registration| registration.judgements)
			.map_or(false, |judgements| {
				judgements
					.iter()
					.any(|(_, j)| matches!(j, Judgement::KnownGood | Judgement::Reasonable))
			})
	}

	fn super_account_id(who: &AccountId) -> Option<AccountId> {
		crate::Identity::super_of(who).map(|parent| parent.0)
	}
}

pub struct AllianceProposalProvider;
impl ProposalProvider<AccountId, Hash, RuntimeCall> for AllianceProposalProvider {
	fn propose_proposal(
		who: AccountId,
		threshold: u32,
		proposal: Box<RuntimeCall>,
		length_bound: u32,
	) -> Result<(u32, u32), DispatchError> {
		AllianceMotion::do_propose_proposed(who, threshold, proposal, length_bound)
	}

	fn vote_proposal(
		who: AccountId,
		proposal: Hash,
		index: ProposalIndex,
		approve: bool,
	) -> Result<bool, DispatchError> {
		AllianceMotion::do_vote(who, proposal, index, approve)
	}

	fn close_proposal(
		proposal_hash: Hash,
		proposal_index: ProposalIndex,
		proposal_weight_bound: Weight,
		length_bound: u32,
	) -> DispatchResultWithPostInfo {
		AllianceMotion::do_close(proposal_hash, proposal_index, proposal_weight_bound, length_bound)
	}

	fn proposal_of(proposal_hash: Hash) -> Option<RuntimeCall> {
		AllianceMotion::proposal_of(proposal_hash)
	}
}

#[cfg(test)]
mod multiplier_tests {
	use frame_support::{
		dispatch::DispatchClass,
		weights::{Weight, WeightToFee},
	};
	use pallet_transaction_payment::{Multiplier, TargetedFeeAdjustment};
	use sp_runtime::{
		assert_eq_error_rate,
		traits::{Convert, One, Zero},
		FixedPointNumber,
	};

	use crate::{
		constants::{currency::*, time::*},
		AdjustmentVariable, MaximumMultiplier, MinimumMultiplier, Runtime,
		RuntimeBlockWeights as BlockWeights, System, TargetBlockFullness, TransactionPayment,
	};

	fn max_normal() -> Weight {
		BlockWeights::get()
			.get(DispatchClass::Normal)
			.max_total
			.unwrap_or_else(|| BlockWeights::get().max_block)
	}

	fn min_multiplier() -> Multiplier {
		MinimumMultiplier::get()
	}

	fn target() -> Weight {
		TargetBlockFullness::get() * max_normal()
	}

	// update based on runtime impl.
	fn runtime_multiplier_update(fm: Multiplier) -> Multiplier {
		TargetedFeeAdjustment::<
			Runtime,
			TargetBlockFullness,
			AdjustmentVariable,
			MinimumMultiplier,
			MaximumMultiplier,
		>::convert(fm)
	}

	// update based on reference impl.
	fn truth_value_update(block_weight: Weight, previous: Multiplier) -> Multiplier {
		let accuracy = Multiplier::accuracy() as f64;
		let previous_float = previous.into_inner() as f64 / accuracy;
		// bump if it is zero.
		let previous_float = previous_float.max(min_multiplier().into_inner() as f64 / accuracy);

		let max_normal = max_normal();
		let target_weight = target();
		let normalized_weight_dimensions = (
			block_weight.ref_time() as f64 / max_normal.ref_time() as f64,
			block_weight.proof_size() as f64 / max_normal.proof_size() as f64,
		);

		let (normal, max, target) =
			if normalized_weight_dimensions.0 < normalized_weight_dimensions.1 {
				(block_weight.proof_size(), max_normal.proof_size(), target_weight.proof_size())
			} else {
				(block_weight.ref_time(), max_normal.ref_time(), target_weight.ref_time())
			};

		// maximum tx weight
		let m = max as f64;
		// block weight always truncated to max weight
		let block_weight = (normal as f64).min(m);
		let v: f64 = AdjustmentVariable::get().to_float();

		// Ideal saturation in terms of weight
		let ss = target as f64;
		// Current saturation in terms of weight
		let s = block_weight;

		let t1 = v * (s / m - ss / m);
		let t2 = v.powi(2) * (s / m - ss / m).powi(2) / 2.0;
		let next_float = previous_float * (1.0 + t1 + t2);
		Multiplier::from_float(next_float)
	}

	fn run_with_system_weight<F>(w: Weight, assertions: F)
	where
		F: Fn() -> (),
	{
		let mut t: sp_io::TestExternalities = frame_system::GenesisConfig::default()
			.build_storage::<Runtime>()
			.unwrap()
			.into();
		t.execute_with(|| {
			System::set_block_consumed_resources(w, 0);
			assertions()
		});
	}

	#[test]
	fn truth_value_update_poc_works() {
		let fm = Multiplier::saturating_from_rational(1, 2);
		let test_set = vec![
			(Weight::zero(), fm),
			(Weight::from_parts(100, 0), fm),
			(Weight::from_parts(1000, 0), fm),
			(target(), fm),
			(max_normal() / 2, fm),
			(max_normal(), fm),
		];
		test_set.into_iter().for_each(|(w, fm)| {
			run_with_system_weight(w, || {
				assert_eq_error_rate!(
					truth_value_update(w, fm),
					runtime_multiplier_update(fm),
					// Error is only 1 in 100^18
					Multiplier::from_inner(100),
				);
			})
		})
	}

	#[test]
	fn multiplier_can_grow_from_zero() {
		// if the min is too small, then this will not change, and we are doomed forever.
		// the block ref time is 1/100th bigger than target.
		run_with_system_weight(target().set_ref_time(target().ref_time() * 101 / 100), || {
			let next = runtime_multiplier_update(min_multiplier());
			assert!(next > min_multiplier(), "{:?} !> {:?}", next, min_multiplier());
		});

		// the block proof size is 1/100th bigger than target.
		run_with_system_weight(target().set_proof_size((target().proof_size() / 100) * 101), || {
			let next = runtime_multiplier_update(min_multiplier());
			assert!(next > min_multiplier(), "{:?} !> {:?}", next, min_multiplier());
		})
	}

	#[test]
	fn multiplier_cannot_go_below_limit() {
		// will not go any further below even if block is empty.
		run_with_system_weight(Weight::zero(), || {
			let next = runtime_multiplier_update(min_multiplier());
			assert_eq!(next, min_multiplier());
		})
	}

	#[test]
	fn time_to_reach_zero() {
		// blocks per 24h in substrate-node: 28,800 (k)
		// s* = 0.1875
		// The bound from the research in an empty chain is:
		// v <~ (p / k(0 - s*))
		// p > v * k * -0.1875
		// to get p == -1 we'd need
		// -1 > 0.00001 * k * -0.1875
		// 1 < 0.00001 * k * 0.1875
		// 10^9 / 1875 < k
		// k > 533_333 ~ 18,5 days.
		run_with_system_weight(Weight::zero(), || {
			// start from 1, the default.
			let mut fm = Multiplier::one();
			let mut iterations: u64 = 0;
			loop {
				let next = runtime_multiplier_update(fm);
				fm = next;
				if fm == min_multiplier() {
					break
				}
				iterations += 1;
			}
			assert!(iterations > 533_333);
		})
	}

	#[test]
	fn min_change_per_day() {
		run_with_system_weight(max_normal(), || {
			let mut fm = Multiplier::one();
			// See the example in the doc of `TargetedFeeAdjustment`. are at least 0.234, hence
			// `fm > 1.234`.
			for _ in 0..DAYS {
				let next = runtime_multiplier_update(fm);
				fm = next;
			}
			assert!(fm > Multiplier::saturating_from_rational(1234, 1000));
		})
	}

	#[test]
	#[ignore]
	fn congested_chain_simulation() {
		// `cargo test congested_chain_simulation -- --nocapture` to get some insight.

		// almost full. The entire quota of normal transactions is taken.
		let block_weight = BlockWeights::get().get(DispatchClass::Normal).max_total.unwrap() -
			Weight::from_parts(100, 0);

		// Default substrate weight.
		let tx_weight = frame_support::weights::constants::ExtrinsicBaseWeight::get();

		run_with_system_weight(block_weight, || {
			// initial value configured on module
			let mut fm = Multiplier::one();
			assert_eq!(fm, TransactionPayment::next_fee_multiplier());

			let mut iterations: u64 = 0;
			loop {
				let next = runtime_multiplier_update(fm);
				// if no change, panic. This should never happen in this case.
				if fm == next {
					panic!("The fee should ever increase");
				}
				fm = next;
				iterations += 1;
				let fee =
					<Runtime as pallet_transaction_payment::Config>::WeightToFee::weight_to_fee(
						&tx_weight,
					);
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
		let fm = Multiplier::saturating_from_rational(1, 2);
		run_with_system_weight(target() / 4, || {
			let next = runtime_multiplier_update(fm);
			assert_eq_error_rate!(
				next,
				truth_value_update(target() / 4, fm),
				Multiplier::from_inner(100),
			);

			// Light block. Multiplier is reduced a little.
			assert!(next < fm);
		});

		run_with_system_weight(target() / 2, || {
			let next = runtime_multiplier_update(fm);
			assert_eq_error_rate!(
				next,
				truth_value_update(target() / 2, fm),
				Multiplier::from_inner(100),
			);
			// Light block. Multiplier is reduced a little.
			assert!(next < fm);
		});
		run_with_system_weight(target(), || {
			let next = runtime_multiplier_update(fm);
			assert_eq_error_rate!(
				next,
				truth_value_update(target(), fm),
				Multiplier::from_inner(100),
			);
			// ideal. No changes.
			assert_eq!(next, fm)
		});
		run_with_system_weight(target() * 2, || {
			// More than ideal. Fee is increased.
			let next = runtime_multiplier_update(fm);
			assert_eq_error_rate!(
				next,
				truth_value_update(target() * 2, fm),
				Multiplier::from_inner(100),
			);

			// Heavy block. Fee is increased a little.
			assert!(next > fm);
		});
	}

	#[test]
	fn weight_mul_grow_on_big_block() {
		run_with_system_weight(target() * 2, || {
			let mut original = Multiplier::zero();
			let mut next = Multiplier::default();

			(0..1_000).for_each(|_| {
				next = runtime_multiplier_update(original);
				assert_eq_error_rate!(
					next,
					truth_value_update(target() * 2, original),
					Multiplier::from_inner(100),
				);
				// must always increase
				assert!(next > original, "{:?} !>= {:?}", next, original);
				original = next;
			});
		});
	}

	#[test]
	fn weight_mul_decrease_on_small_block() {
		run_with_system_weight(target() / 2, || {
			let mut original = Multiplier::saturating_from_rational(1, 2);
			let mut next;

			for _ in 0..100 {
				// decreases
				next = runtime_multiplier_update(original);
				assert!(next < original, "{:?} !<= {:?}", next, original);
				original = next;
			}
		})
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		let kb_time = Weight::from_parts(1024, 0);
		let kb_size = Weight::from_parts(0, 1024);
		let mb_time = 1024u64 * kb_time;
		let max_fm = Multiplier::saturating_from_integer(i128::MAX);

		// check that for all values it can compute, correctly.
		vec![
			Weight::zero(),
			// testcases ignoring proof size part of the weight.
			Weight::from_parts(1, 0),
			Weight::from_parts(10, 0),
			Weight::from_parts(1000, 0),
			kb_time,
			10u64 * kb_time,
			100u64 * kb_time,
			mb_time,
			10u64 * mb_time,
			Weight::from_parts(2147483647, 0),
			Weight::from_parts(4294967295, 0),
			// testcases ignoring ref time part of the weight.
			Weight::from_parts(0, 100000000000),
			1000000u64 * kb_size,
			1000000000u64 * kb_size,
			Weight::from_parts(0, 18014398509481983),
			Weight::from_parts(0, 9223372036854775807),
			// test cases with both parts of the weight.
			BlockWeights::get().max_block / 1024,
			BlockWeights::get().max_block / 2,
			BlockWeights::get().max_block,
			Weight::MAX / 2,
			Weight::MAX,
		]
		.into_iter()
		.for_each(|i| {
			run_with_system_weight(i, || {
				let next = runtime_multiplier_update(Multiplier::one());
				let truth = truth_value_update(i, Multiplier::one());
				assert_eq_error_rate!(truth, next, Multiplier::from_inner(50_000_000));
			});
		});

		// Some values that are all above the target and will cause an increase.
		let t = target();
		vec![
			t + Weight::from_parts(100, 0),
			t + Weight::from_parts(0, t.proof_size() * 2),
			t * 2,
			t * 4,
		]
		.into_iter()
		.for_each(|i| {
			run_with_system_weight(i, || {
				let fm = runtime_multiplier_update(max_fm);
				// won't grow. The convert saturates everything.
				assert_eq!(fm, max_fm);
			})
		});
	}
}
