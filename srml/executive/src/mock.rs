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

//! Test utilities

#![cfg(test)]

use super::*;
use runtime_io;
use substrate_primitives::{Blake2Hasher};
use srml_support::{impl_outer_origin, impl_outer_event, impl_outer_dispatch, parameter_types};
use primitives::traits::{IdentityLookup, BlakeTwo256};
use primitives::testing::{Header, Block};
use system;
pub use balances::Call as balancesCall;
pub use system::Call as systemCall;

impl_outer_origin! {
    pub enum Origin for Runtime {
    }
}

impl_outer_event!{
    pub enum MetaEvent for Runtime {
        balances<T>,
    }
}

impl_outer_dispatch! {
	pub enum Call for Runtime where origin: Origin {
		balances::Balances,
		system::System,
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Eq, PartialEq)]
pub struct Runtime;
parameter_types! {
    pub const BlockHashCount: u64 = 250;
}

impl system::Trait for Runtime {
    type Origin = Origin;
    type Index = u64;
    type BlockNumber = u64;
    type Hash = substrate_primitives::H256;
    type Hashing = BlakeTwo256;
    type AccountId = u64;
    type Lookup = IdentityLookup<u64>;
    type Header = Header;
    type WeightMultiplierUpdate = ();
    type BlockHashCount = BlockHashCount;
    type Event = MetaEvent;
}
parameter_types! {
    pub const ExistentialDeposit: u64 = 0;
    pub const TransferFee: u64 = 0;
    pub const CreationFee: u64 = 0;
    pub const TransactionBaseFee: u64 = 0;
    pub const TransactionByteFee: u64 = 0;
}
impl balances::Trait for Runtime {
    type Balance = u64;
    type OnFreeBalanceZero = ();
    type OnNewAccount = ();
    type Event = MetaEvent;
    type TransactionPayment = ();
    type DustRemoval = ();
    type TransferPayment = ();
    type ExistentialDeposit = ExistentialDeposit;
    type TransferFee = TransferFee;
    type CreationFee = CreationFee;
    type TransactionBaseFee = TransactionBaseFee;
    type TransactionByteFee = TransactionByteFee;
}

impl ValidateUnsigned for Runtime {
    type Call = Call;

    fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
        match call {
            Call::Balances(balancesCall::set_balance(_, _, _)) => TransactionValidity::Valid {
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
    let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 1000_000_000)],
        vesting: vec![],
    }.build_storage().unwrap().0);
    t.into()
}

type Balances = balances::Module<Runtime>;
type System = system::Module<Runtime>;

pub type TestXt = primitives::testing::TestXt<Call>;
pub type Executive = super::Executive<
    Runtime,
    Block<TestXt>,
    system::ChainContext<Runtime>,
    balances::Module<Runtime>,
    Runtime,
    ()
>;
