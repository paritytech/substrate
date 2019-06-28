// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Test utilities

#![cfg(test)]

use super::*;
use runtime_io;
use substrate_primitives::{Blake2Hasher};
use srml_support::{impl_outer_origin, impl_outer_event};
use primitives::{BuildStorage, Perbill};
use primitives::traits::{IdentityLookup, Convert, BlakeTwo256};
use primitives::testing::{Digest, DigestItem, Header, Block};
use primitives::weights::{Weight, MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT};
use system;
use balances::Call;

// DummyWeightToFeeHandler
// 
// stateful testing of fee multiplier calculations
pub struct DummyFeeHandler;
impl Convert<Weight, u64> for DummyFeeHandler {
	fn convert(weight: Weight) -> u64 {
		let billion = 1_000_000_000_u128;
		let ideal = IDEAL_TRANSACTIONS_WEIGHT as u128;
        let max = MAX_TRANSACTIONS_WEIGHT as u128;
		let all = (<system::Module<Runtime>>::all_extrinsics_weight() + weight) as u128;
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

        // useful for testing
        //println!("Fee Multiplier: {}", fee_multiplier);
		let p = Perbill::from_parts(fee_multiplier.min(billion) as u32);
		let transaction_fee: u32 = p * weight;
		transaction_fee.into()
	}
}

impl_outer_origin! {
    pub enum Origin for Runtime {
    }
}

impl_outer_event!{
    pub enum MetaEvent for Runtime {
        balances<T>,
    }
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Eq, PartialEq)]
pub struct Runtime;
impl system::Trait for Runtime {
    type Origin = Origin;
    type Index = u64;
    type BlockNumber = u64;
    type Hash = substrate_primitives::H256;
    type Hashing = BlakeTwo256;
    type Digest = Digest;
    type AccountId = u64;
    type Lookup = IdentityLookup<u64>;
    type Header = Header;
    type Event = MetaEvent;
    type Log = DigestItem;
}
impl balances::Trait for Runtime {
    type Balance = u64;
    type WeightToFee = DummyFeeHandler;
    type OnFreeBalanceZero = ();
    type OnNewAccount = ();
    type Event = MetaEvent;
    type TransactionPayment = ();
    type DustRemoval = ();
    type TransferPayment = ();
}

impl ValidateUnsigned for Runtime {
    type Call = Call<Runtime>;

    fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
        match call {
            Call::set_balance(_, _, _) => TransactionValidity::Valid {
                priority: 0,
                requires: vec![],
                provides: vec![],
                longevity: std::u64::MAX,
                propagate: false,
            },
            _ => TransactionValidity::Invalid(0),
        }
    }
}

pub fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
    let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime>::default().build_storage().unwrap().0);
    t.into()
}

pub fn poc(weight: Weight, already_existing_weight: Weight) -> u64  {
    // derived from node/runtime (this version type aliases Balance as u32)
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
    (weight * fm) as u64
}

pub type TestXt = primitives::testing::TestXt<Call<Runtime>>;
pub type Executive = super::Executive<Runtime, Block<TestXt>, system::ChainContext<Runtime>, balances::Module<Runtime>, Runtime, ()>;