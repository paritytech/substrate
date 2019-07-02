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
use runtime_primitives::weights::{Weight, MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT};
use runtime_primitives::traits::{Convert, Zero};
use crate::{Runtime, Perbill, Balances};

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
pub struct WeightToFeeHandler;
impl Convert<Weight, Balance> for WeightToFeeHandler {
	fn convert(weight: Weight) -> Balance {
		let max_fraction = 1_000_000_000_u128;
		let ideal = IDEAL_TRANSACTIONS_WEIGHT as u128;
		let max = MAX_TRANSACTIONS_WEIGHT as u128;
		let all =
			(<system::Module<Runtime>>::all_extrinsics_weight() as u128)
			.saturating_add(weight as u128);

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
		let mut positive = false;
		let diff = match ideal.checked_sub(all) {
			Some(d) => d,
			None => { positive = true; all - ideal }
		};

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = 40_000;
		// 0.00004^2 = 16/10^10 ~= 2/10^9
		let v_squared = 2;

		let mut first_term = v;
		first_term = collapse_mul(first_term, from_max_to_per_fraction(diff));
		first_term = first_term / max_fraction;

		// It is very unlikely that this will exist (in our poor perbill estimate) but we are giving it
		// a shot.
		let mut second_term = v_squared;
		second_term = collapse_mul(second_term, from_max_to_per_fraction(diff));
		second_term = collapse_mul(second_term, from_max_to_per_fraction(diff) / 2);
		second_term = second_term / max_fraction;
		second_term = second_term / max_fraction;

		if positive {
			let excess = first_term.saturating_add(second_term);
			let p = Perbill::from_parts(excess.min(max_fraction) as u32);
			Balance::from(weight).saturating_add(Balance::from(p * weight))
		} else {
			// first_term > second_term
			let negative = first_term - second_term;
			let p = Perbill::from_parts((max_fraction - negative) as u32);
			Balance::from(p * weight)
		}.into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_primitives::{
		weights::{MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT, Weight},
		traits::{IdentityLookup, Convert, BlakeTwo256},
		testing::Header,
	};
	use support::impl_outer_origin;
	use substrate_primitives::{H256, Blake2Hasher};
	use runtime_io::with_externalities;

	impl_outer_origin!{
		pub enum Origin for Runtime {}
	}

	// needed because WeightToFeeHandler uses system module internally.
	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Runtime;
	impl system::Trait for Runtime {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
	}

	type System = system::Module<Runtime>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0.into()
	}

	fn weight_to_fee(weight: Weight, already_existing_weight: Weight) -> Balance  {
		let weight = weight as f32;
		let already_existing_weight = already_existing_weight as f32;
		let v = 0.00004;

		// maximum tx weight
		let m = MAX_TRANSACTIONS_WEIGHT as f32;
		// Ideal saturation in terms of weight
		let ss = IDEAL_TRANSACTIONS_WEIGHT as f32;
		// Current saturation in terms of weight
		let s = already_existing_weight + weight;

		let fm = 1.0 + (v * (s/m - ss/m)) + (v.powi(2) * (s/m - ss/m).powi(2)) / 2.0;
		(weight * fm) as Balance
	}

	#[test]
	fn stateless_weight_fee() {
		with_externalities(&mut new_test_ext(), || {
			let ideal = IDEAL_TRANSACTIONS_WEIGHT;
			let max = MAX_TRANSACTIONS_WEIGHT;
			// NOTE: this is now accurate enough for weights below 4194304. Might need change later
			// on with new weight values
			// (1) Typical low-cost transaction
			// (2) Close to ideal. Fee is less than size.
			// (3) 5 below the ideal, Less fee.
			// (4) 5 above the ideal
			// (6) largest number allowed (note: max weight is 4194304)
			let inputs = vec![28, ideal/2, ideal/2 + 5_000, ideal/2 + 10_000, ideal, ideal + 1000, max / 2, max];
			inputs.into_iter().for_each(|i| {
				let diff = WeightToFeeHandler::convert(i) as i64 - weight_to_fee(i, 0) as i64;
				assert!(diff < 4)
			});
		})
	}

	#[test]
	fn weight_to_fee_should_not_overflow_on_large_weights() {
		with_externalities(&mut new_test_ext(), || {
			let kb = 1024_u32;
			let mb = kb * kb;
			vec![0, 1, 10, 1000, kb, 10 * kb, 100 * kb, mb, 10 * mb, Weight::max_value() / 2, Weight::max_value()]
				.into_iter()
				.for_each(|i| { WeightToFeeHandler::convert(i); });
		})
	}

	#[test]
	fn stateful_weight_to_fee() {
		with_externalities(&mut new_test_ext(), || {
			// below ideal: we charge a bit less.
			assert!(WeightToFeeHandler::convert(1_000_000) < 1_000_000);

			System::note_applied_extrinsic(&Ok(()), IDEAL_TRANSACTIONS_WEIGHT * 3);
			assert_eq!(System::all_extrinsics_weight(), 3 * IDEAL_TRANSACTIONS_WEIGHT);

			// above ideal: we charge a bit more.
			assert!(WeightToFeeHandler::convert(1_000_000) > 1_000_000);
		})
	}
}
