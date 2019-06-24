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
use runtime_primitives::traits::Convert;
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
pub struct WeightToFeeHandler;
impl Convert<Weight, Balance> for WeightToFeeHandler {
	fn convert(weight: Weight) -> Balance {
		let billion = 1_000_000_000_u128;
		let ideal = IDEAL_TRANSACTIONS_WEIGHT as u128;
        let max = MAX_TRANSACTIONS_WEIGHT as u128;
		let all = <system::Module<Runtime>>::all_extrinsics_weight() as u128 + weight as u128;
		let from_max_to_per_bill = |x| { x * billion / max };

		// determines if the first_term is positive and compute diff.
		let mut positive = false;
		let diff = match ideal.checked_sub(all) {
			Some(d) => d,
			None => { positive = true; all - ideal }
		};

		// 0.00004 = 4/100_000 = 40_000/10^9
		let v = 40_000;
		// 0.00004^2 = 16/10^10 ~= 2/10^9
		let v_squared = 2;

		let mut first_term = v * from_max_to_per_bill(diff);
		first_term = first_term / billion;

		let mut second_term = v_squared * from_max_to_per_bill(diff) * from_max_to_per_bill(diff) / 2;
		second_term = second_term / billion;
		second_term = second_term / billion;

		//					   = 1		+ second_term
		let mut fee_multiplier = billion + second_term;
		fee_multiplier = if positive { fee_multiplier + first_term } else { fee_multiplier - first_term};

		let p = Perbill::from_parts(fee_multiplier.min(billion) as u32);
		let transaction_fee: u32 = p * weight;
		transaction_fee.into()
	}
}

#[cfg(test)]
mod tests {
    use super::*;
    use runtime_primitives::{
        weights::{MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT, Weight},
        traits::{IdentityLookup, Convert, BlakeTwo256},
        testing::{Digest, DigestItem, Header},
        BuildStorage,
    };
    use support::impl_outer_origin;
    use substrate_primitives::{H256, Blake2Hasher};
    use runtime_io::with_externalities;

    impl_outer_origin!{
        pub enum Origin for Runtime {}
    }

    // Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
    #[derive(Clone, PartialEq, Eq, Debug)]
    pub struct Runtime;
    impl system::Trait for Runtime {
        type Origin = Origin;
        type Index = u64;
        type BlockNumber = u64;
        type Hash = H256;
        type Hashing = BlakeTwo256;
        type Digest = Digest;
        type AccountId = u64;
        type Lookup = IdentityLookup<Self::AccountId>;
        type Header = Header;
        type Event = ();
        type Log = DigestItem;
    }
    impl balances::Trait for Runtime {
        type Balance = u128;
        type WeightToFee = WeightToFeeHandler;
        type OnFreeBalanceZero = ();
        type OnNewAccount = ();
        type Event = ();
        type TransactionPayment = ();
        type DustRemoval = ();
        type TransferPayment = ();
    }

    fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
		t.extend(balances::GenesisConfig::<Runtime>::default().build_storage().unwrap().0);
		t.into()
	}

    fn poc(weight: Weight, already_existing_weight: Weight) -> Balance  {
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
    fn weight_to_fee_works_for_all_weight_ranges() {
        with_externalities(&mut new_test_ext(), || {
            // NOTE: u32::max_value() cannot be accurately calcualted with per_billion.
            vec![0, 1, 100, 10000, 300_000_000, u32::max_value()/2, u32::max_value()-1]
                .into_iter()
                .for_each(|i| assert_eq!(WeightToFeeHandler::convert(i), poc(i, 0)));
        })
    }

    #[test]
	fn stateless_weight_fee_range() {
        with_externalities(&mut new_test_ext(), || {
            // (1) Typical low-cost transaction.
            assert_eq!(WeightToFeeHandler::convert(28), 27);
            // (2) Close to ideal. Fee is less than size.
            assert_eq!(
                WeightToFeeHandler::convert(IDEAL_TRANSACTIONS_WEIGHT/2),
                (IDEAL_TRANSACTIONS_WEIGHT/2 - 3).into()
            );
            // (3) 5 below the ideal, Less fee.
            assert_eq!(
                WeightToFeeHandler::convert(IDEAL_TRANSACTIONS_WEIGHT/2 + 5_000),
                (IDEAL_TRANSACTIONS_WEIGHT/2 + 4_997).into()
            );
            // (4) 5 above the ideal,
            assert_eq!(
                WeightToFeeHandler::convert(IDEAL_TRANSACTIONS_WEIGHT + 10_000),
                (IDEAL_TRANSACTIONS_WEIGHT + 10_000).into()
            );
            assert_eq!(WeightToFeeHandler::convert((1024 * 1024) + 87_381), 1135957);
            // (5) 1 below maximum
            assert_eq!(WeightToFeeHandler::convert((4 * 1024 * 1024) - 1), 4194303);
            // (6) maximum weight
            assert_eq!(WeightToFeeHandler::convert(4 * 1024 * 1024), 4194304);
            // (7) above maximum
            assert_eq!(WeightToFeeHandler::convert((4 * 1024 * 1024) + 1), 4194305);
        })
	}

    #[test]
    #[ignore]
    fn statefull_weight_fee_range() {
        unimplemented!();
    }
}