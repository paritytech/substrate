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

//! Tests for the module.

#![cfg(test)]

use super::*;
use mock::{new_test_ext, TestXt, Executive, Runtime, Call, systemCall, balancesCall};
use system;
use primitives::weights::{MAX_TRANSACTIONS_WEIGHT};
use primitives::testing::{Digest, Header, Block};
use primitives::traits::{Header as HeaderT};
use substrate_primitives::{Blake2Hasher, H256};
use runtime_io::with_externalities;
use srml_support::traits::Currency;
use hex_literal::hex;

#[test]
fn balance_transfer_dispatch_works() {
    let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 129)],
        vesting: vec![],
    }.build_storage().unwrap().0);
    let xt = primitives::testing::TestXt(Some(1), 0, Call::Balances(balancesCall::transfer(2, 69)));
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    with_externalities(&mut t, || {
        Executive::initialize_block(
            &Header::new(1, H256::default(), H256::default(),[69u8; 32].into(), Digest::default())
        );
        assert_eq!(Executive::apply_extrinsic(xt.clone()).unwrap(), ApplyOutcome::Success);
        // default fee.
        assert_eq!(<balances::Module<Runtime>>::total_balance(&1), 129 - 69 - 29);
        assert_eq!(<balances::Module<Runtime>>::total_balance(&2), 69);
    });
}

#[test]
fn block_import_works() {
    with_externalities(&mut new_test_ext(), || {
        Executive::execute_block(Block {
            header: Header {
                parent_hash: [69u8; 32].into(),
                number: 1,
                state_root: hex!("5518fc5383e35df8bf7cda7d6467d1307cc907424b7c8633148163aba5ee6aa8").into(),
                extrinsics_root: hex!("03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314").into(),
                digest: Digest { logs: vec![], },
            },
            extrinsics: vec![],
        });
    });
}

#[test]
#[should_panic]
fn block_import_of_bad_state_root_fails() {
    with_externalities(&mut new_test_ext(), || {
        Executive::execute_block(Block {
            header: Header {
                parent_hash: [69u8; 32].into(),
                number: 1,
                state_root: [0u8; 32].into(),
                extrinsics_root: hex!("03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314").into(),
                digest: Digest { logs: vec![], },
            },
            extrinsics: vec![],
        });
    });
}

#[test]
#[should_panic]
fn block_import_of_bad_extrinsic_root_fails() {
    with_externalities(&mut new_test_ext(), || {
        Executive::execute_block(Block {
            header: Header {
                parent_hash: [69u8; 32].into(),
                number: 1,
                state_root: hex!("49cd58a254ccf6abc4a023d9a22dcfc421e385527a250faec69f8ad0d8ed3e48").into(),
                extrinsics_root: [0u8; 32].into(),
                digest: Digest { logs: vec![], },
            },
            extrinsics: vec![],
        });
    });
}

#[test]
fn bad_extrinsic_not_inserted() {
    let mut t = new_test_ext();
    let xt = primitives::testing::TestXt(Some(1), 42, Call::Balances(balancesCall::transfer(33, 69)));
    with_externalities(&mut t, || {
        Executive::initialize_block(&Header::new(1, H256::default(), H256::default(),
                                                [69u8; 32].into(), Digest::default()));
        assert!(Executive::apply_extrinsic(xt).is_err());
        assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(0));
    });
}

#[test]
fn block_weight_limit_enforced() {
    let run_test = |should_fail: bool| {
        let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
        t.extend(balances::GenesisConfig::<Runtime> {
            balances: vec![(1, 129)],
            vesting: vec![],
        }.build_storage().unwrap().0);
        let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
        let xt = primitives::testing::TestXt(Some(1), 0, Call::Balances(balancesCall::transfer(1, 15)));
        let xt2 = primitives::testing::TestXt(Some(1), 1, Call::Balances(balancesCall::transfer(2, 30)));
        let encoded = xt2.encode();
        let len = if should_fail { (MAX_TRANSACTIONS_WEIGHT - 1) as usize } else { encoded.len() };
        with_externalities(&mut t, || {
            Executive::initialize_block(&Header::new(
                1,
                H256::default(),
                H256::default(),
                [69u8; 32].into(),
                Digest::default()
            ));
            assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
            assert_eq!(Executive::apply_extrinsic(xt).unwrap(), ApplyOutcome::Success);
            let res = Executive::apply_extrinsic_with_len(xt2, len, Some(encoded));

            if should_fail {
                assert!(res.is_err());
                assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 28);
                assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(1));
            } else {
                assert!(res.is_ok());
                assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 56);
                assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(2));
            }
        });
    };

    run_test(false);
    run_test(true);
}

#[test]
fn exceeding_block_weight_fails() {
    let mut t = new_test_ext();
    let xt = |i: u32|
        primitives::testing::TestXt(
            Some(1),
            i.into(),
            Call::System(systemCall::remark(vec![0_u8; 1024 * 128]))
        );
    with_externalities(&mut t, || {
        let len = xt(0).clone().encode().len() as u32;
        let xts_to_overflow = MAX_TRANSACTIONS_WEIGHT / len;
        let xts: Vec<TestXt> = (0..xts_to_overflow).map(|i| xt(i) ).collect::<_>();

        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
        let _ = xts.into_iter().for_each(|x| assert_eq!(
            Executive::apply_extrinsic(x).unwrap(),
            ApplyOutcome::Success
        ));
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), xts_to_overflow * len);

        // next one will be rejected.
        assert_eq!(Executive::apply_extrinsic(xt(xts_to_overflow)).err().unwrap(), ApplyError::FullBlock);
    });
}

#[test]
fn default_block_weight() {
    let len = primitives::testing::TestXt(Some(1), 0, Call::Balances(balancesCall::transfer(69, 10)))
        .encode()
        .len() as u32;
    let mut t = new_test_ext();
    with_externalities(&mut t, || {
        assert_eq!(
            Executive::apply_extrinsic(
                primitives::testing::TestXt(Some(1), 0, Call::Balances(balancesCall::transfer(69, 10)))
            ).unwrap(),
            ApplyOutcome::Success
        );
        assert_eq!(
            Executive::apply_extrinsic(
                primitives::testing::TestXt(Some(1), 1, Call::Balances(balancesCall::transfer(69, 10)))
            ).unwrap(),
            ApplyOutcome::Success
        );
        assert_eq!(
            Executive::apply_extrinsic(
                primitives::testing::TestXt(Some(1), 2, Call::Balances(balancesCall::transfer(69, 10)))
            ).unwrap(),
            ApplyOutcome::Success
        );
        assert_eq!(
            <system::Module<Runtime>>::all_extrinsics_weight(),
            3 * (0 /*base*/ + len /*len*/ * 1 /*byte*/)
        );
    });
}

#[test]
fn fail_on_bad_nonce() {
    let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 129)],
        vesting: vec![],
    }.build_storage().unwrap().0);
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    let xt = primitives::testing::TestXt(Some(1), 0, Call::Balances(balancesCall::transfer(1, 15)));
    let xt2 = primitives::testing::TestXt(Some(1), 10, Call::Balances(balancesCall::transfer(1, 15)));
    with_externalities(&mut t, || {
        Executive::apply_extrinsic(xt).unwrap();
        let res = Executive::apply_extrinsic(xt2);
        assert_eq!(res, Err(ApplyError::Future));
    });
}

#[test]
fn validate_unsigned() {
    let xt = primitives::testing::TestXt(None, 0, Call::Balances(balancesCall::set_balance(33, 69, 69)));
    let valid = TransactionValidity::Valid {
        priority: 0,
        requires: vec![],
        provides: vec![],
        longevity: 18446744073709551615,
        propagate: false,
    };
    let mut t = new_test_ext();

    with_externalities(&mut t, || {
        assert_eq!(Executive::validate_transaction(xt.clone()), valid);
        assert_eq!(Executive::apply_extrinsic(xt), Ok(ApplyOutcome::Fail));
    });
}
