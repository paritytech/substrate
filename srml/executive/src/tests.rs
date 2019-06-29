// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use mock::{new_test_ext, poc};
use mock::{TestXt, Executive, DummyFeeHandler, Runtime};
use balances::Call;
use system;
use primitives::BuildStorage;
use primitives::weights::{Weight, MAX_TRANSACTIONS_WEIGHT, IDEAL_TRANSACTIONS_WEIGHT};
use primitives::testing::{Digest, Header, Block}; //DigestItem
use primitives::traits::{Header as HeaderT, Convert};
use substrate_primitives::{Blake2Hasher, H256};
use runtime_io::with_externalities;
use srml_support::traits::Currency;
use hex_literal::hex;

#[test]
fn balance_transfer_dispatch_works() {
    let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 129)],
        existential_deposit: 0,
        transfer_fee: 0,
        creation_fee: 0,
        vesting: vec![],
    }.build_storage().unwrap().0);
    let xt = primitives::testing::TestXt(Some(1), 0, Call::transfer(2, 69));
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    with_externalities(&mut t, || {
        Executive::initialize_block(&Header::new(1, H256::default(), H256::default(),
            [69u8; 32].into(), Digest::default()));
        Executive::apply_extrinsic(xt).unwrap();
        assert_eq!(<balances::Module<Runtime>>::total_balance(&1), 33);
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
                state_root: hex!("f1abdf2b1192e089c432b48a7dd4b35adf732ad756eb6771fbb74e014f36d7e3").into(),
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
    let xt = primitives::testing::TestXt(Some(1), 42, Call::transfer(33, 69));
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
        let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
        t.extend(balances::GenesisConfig::<Runtime> {
            balances: vec![(1, 129)],
            existential_deposit: 0,
            transfer_fee: 0,
            creation_fee: 0,
            vesting: vec![],
        }.build_storage().unwrap().0);
        let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
        let xt = primitives::testing::TestXt(Some(1), 0, Call::transfer(1, 15));
        let xt2 = primitives::testing::TestXt(Some(1), 1, Call::transfer(2, 30));
        let encoded = xt2.encode();
        let len = if should_fail { (MAX_TRANSACTIONS_WEIGHT - 1) as usize } else { encoded.len() };
        with_externalities(&mut t, || {
            Executive::initialize_block(&Header::new(
                1, 
                H256::default(), H256::default(), 
                [69u8; 32].into(),
                Digest::default()
            ));
            assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
            Executive::apply_extrinsic(xt).unwrap();
            let res = Executive::apply_extrinsic_with_len(xt2, len, Some(encoded));

            if should_fail {
                assert!(res.is_err());
                assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 27);
                assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(1));
            } else {
                assert!(res.is_ok());
                assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 54);
                assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(2));
            }
        });
    };

    run_test(false);
    run_test(true);
}

#[test]
fn tipping_block_weight() {
    let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 500)],
        existential_deposit: 0,
        transfer_fee: 0,
        creation_fee: 0,
        vesting: vec![],
    }.build_storage().unwrap().0);
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    let xt = primitives::testing::TestXt(Some(1), 0, Call::transfer(33, 69));
    let xt1 = primitives::testing::TestXt(Some(1), 1, Call::transfer(33, 69));
    let xt2 = primitives::testing::TestXt(Some(1), 2, Call::transfer(33, 69));
    let xt3 = primitives::testing::TestXt(Some(1), 3, Call::transfer(33, 69));
    let xt4 = primitives::testing::TestXt(Some(1), 4, Call::transfer(33, 69));
    let xt5 = primitives::testing::TestXt(Some(1), 5, Call::transfer(33, 69));
    let encoded = xt5.encode();
    let len = (MAX_TRANSACTIONS_WEIGHT - 139) as usize;
    with_externalities(&mut t, || {
        Executive::initialize_block(&<Header as HeaderT>::new(1, H256::default(), H256::default(),
                                    [69u8; 32].into(), Digest::default()));
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);

        Executive::apply_extrinsic(xt).unwrap();
        Executive::apply_extrinsic(xt1).unwrap();
        Executive::apply_extrinsic(xt2).unwrap();
        Executive::apply_extrinsic(xt3).unwrap();
        Executive::apply_extrinsic(xt4).unwrap();
        let res = Executive::apply_extrinsic_with_len(xt5, len, Some(encoded));
        assert!(res.is_err());
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 140);
        assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(5));
    });
}

#[test]
fn default_block_weight() {
    let xt = primitives::testing::TestXt(None, 0, Call::set_balance(33, 69, 69));
    let mut t = new_test_ext();
    with_externalities(&mut t, || {
        Executive::apply_extrinsic(xt.clone()).unwrap();
        Executive::apply_extrinsic(xt.clone()).unwrap();
        Executive::apply_extrinsic(xt.clone()).unwrap();
        assert_eq!(
            <system::Module<Runtime>>::all_extrinsics_weight(),
            3 * (0 /*base*/ + 22 /*len*/ * 1 /*byte*/)
        );
    });
}

#[test]
fn fail_on_bad_nonce() {
    let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 129)],
        existential_deposit: 0,
        transfer_fee: 0,
        creation_fee: 0,
        vesting: vec![],
    }.build_storage().unwrap().0);
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    let xt = primitives::testing::TestXt(Some(1), 0, Call::transfer(1, 15));
    let xt2 = primitives::testing::TestXt(Some(1), 10, Call::transfer(1, 15));
    with_externalities(&mut t, || {
        Executive::apply_extrinsic(xt).unwrap();
        let res = Executive::apply_extrinsic(xt2);
        assert_eq!(res, Err(ApplyError::Future));
    });
}

#[test]
fn validate_unsigned() {
    let xt = primitives::testing::TestXt(None, 0, Call::set_balance(33, 69, 69));
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

#[test]
fn stateful_weight_fee_range() {
    let mut t = system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0;
    t.extend(balances::GenesisConfig::<Runtime> {
        balances: vec![(1, 1000), (2, 1000), (3, 1000)],
        existential_deposit: 0,
        transfer_fee: 0,
        creation_fee: 0,
        vesting: vec![],
    }.build_storage().unwrap().0);
    let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
    let xt1 = primitives::testing::TestXt(Some(1), 0, Call::transfer(33, 69));
    let t1 = xt1.encode();
    let xt2 = primitives::testing::TestXt(Some(2), 0, Call::transfer(33, 69));
    let t2 = xt2.encode();
    let xt3 = primitives::testing::TestXt(Some(3), 0, Call::transfer(33, 69));
    let t3 = xt3.encode();
    // length is constant to test fee variation as block weight increases
    let const_len = 300 as usize; // largest usize allowed for apply_extrinsic_with_len
    with_externalities(&mut t, || {
        Executive::initialize_block(&Header::new(1, H256::default(), H256::default(),
    								[69u8; 32].into(), Digest::default()));
    	assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);

        assert_eq!(DummyFeeHandler::convert(300), poc(300, 0));
        assert_eq!(DummyFeeHandler::convert(300), 299);
        let res = Executive::apply_extrinsic_with_len(xt1, const_len, Some(t1));
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 300);

        assert_eq!(DummyFeeHandler::convert(300), poc(300, 300));
        assert_eq!(DummyFeeHandler::convert(300), 299);
        let res = Executive::apply_extrinsic_with_len(xt2, const_len, Some(t2));
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 600);

        assert_eq!(DummyFeeHandler::convert(300), poc(300, 600));
        assert_eq!(DummyFeeHandler::convert(300), 299);
        let res = Executive::apply_extrinsic_with_len(xt3, const_len, Some(t3));
        assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 900);

        assert_ne!(DummyFeeHandler::convert(300), poc(300, 10000000));
    });
}