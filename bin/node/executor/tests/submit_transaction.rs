// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use codec::Decode;
use frame_system::offchain::{SendSignedTransaction, Signer, SubmitTransaction};
use node_runtime::{Executive, Indices, Runtime, UncheckedExtrinsic};
use sp_application_crypto::AppKey;
use sp_core::offchain::{testing::TestTransactionPoolExt, TransactionPoolExt};
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStore};
use std::sync::Arc;

pub mod common;
use self::common::*;

#[test]
fn should_submit_unsigned_transaction() {
	let mut t = new_test_ext(compact_code_unwrap(), false);
	let (pool, state) = TestTransactionPoolExt::new();
	t.register_extension(TransactionPoolExt::new(pool));

	t.execute_with(|| {
		let signature = Default::default();
		let heartbeat_data = pallet_im_online::Heartbeat {
			block_number: 1,
			network_state: Default::default(),
			session_index: 1,
			authority_index: 0,
			validators_len: 0,
		};

		let call = pallet_im_online::Call::heartbeat(heartbeat_data, signature);
		SubmitTransaction::<Runtime, pallet_im_online::Call<Runtime>>::submit_unsigned_transaction(
			call.into(),
		)
		.unwrap();

		assert_eq!(state.read().transactions.len(), 1)
	});
}

const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";

#[test]
fn should_submit_signed_transaction() {
	let mut t = new_test_ext(compact_code_unwrap(), false);
	let (pool, state) = TestTransactionPoolExt::new();
	t.register_extension(TransactionPoolExt::new(pool));

	let keystore = KeyStore::new();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter1", PHRASE)),
	)
	.unwrap();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter2", PHRASE)),
	)
	.unwrap();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter3", PHRASE)),
	)
	.unwrap();
	t.register_extension(KeystoreExt(Arc::new(keystore)));

	t.execute_with(|| {
		let results =
			Signer::<Runtime, TestAuthorityId>::all_accounts().send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});

		let len = results.len();
		assert_eq!(len, 3);
		assert_eq!(results.into_iter().filter_map(|x| x.1.ok()).count(), len);
		assert_eq!(state.read().transactions.len(), len);
	});
}

#[test]
fn should_submit_signed_twice_from_the_same_account() {
	let mut t = new_test_ext(compact_code_unwrap(), false);
	let (pool, state) = TestTransactionPoolExt::new();
	t.register_extension(TransactionPoolExt::new(pool));

	let keystore = KeyStore::new();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter1", PHRASE)),
	)
	.unwrap();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter2", PHRASE)),
	)
	.unwrap();
	t.register_extension(KeystoreExt(Arc::new(keystore)));

	t.execute_with(|| {
		let result =
			Signer::<Runtime, TestAuthorityId>::any_account().send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});

		assert!(result.is_some());
		assert_eq!(state.read().transactions.len(), 1);

		// submit another one from the same account. The nonce should be incremented.
		let result =
			Signer::<Runtime, TestAuthorityId>::any_account().send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});

		assert!(result.is_some());
		assert_eq!(state.read().transactions.len(), 2);

		// now check that the transaction nonces are not equal
		let s = state.read();
		fn nonce(tx: UncheckedExtrinsic) -> frame_system::CheckNonce<Runtime> {
			let extra = tx.signature.unwrap().2;
			extra.4
		}
		let nonce1 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[0]).unwrap());
		let nonce2 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[1]).unwrap());
		assert!(nonce1 != nonce2, "Transactions should have different nonces. Got: {:?}", nonce1);
	});
}

#[test]
fn should_submit_signed_twice_from_all_accounts() {
	let mut t = new_test_ext(compact_code_unwrap(), false);
	let (pool, state) = TestTransactionPoolExt::new();
	t.register_extension(TransactionPoolExt::new(pool));

	let keystore = KeyStore::new();
	keystore
		.sr25519_generate_new(sr25519::AuthorityId::ID, Some(&format!("{}/hunter1", PHRASE)))
		.unwrap();
	keystore
		.sr25519_generate_new(sr25519::AuthorityId::ID, Some(&format!("{}/hunter2", PHRASE)))
		.unwrap();
	t.register_extension(KeystoreExt(Arc::new(keystore)));

	t.execute_with(|| {
		let results = Signer::<Runtime, TestAuthorityId>::all_accounts()
			.send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});

		let len = results.len();
		assert_eq!(len, 2);
		assert_eq!(results.into_iter().filter_map(|x| x.1.ok()).count(), len);
		assert_eq!(state.read().transactions.len(), 2);

		// submit another one from the same account. The nonce should be incremented.
		let results = Signer::<Runtime, TestAuthorityId>::all_accounts()
			.send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});

		let len = results.len();
		assert_eq!(len, 2);
		assert_eq!(results.into_iter().filter_map(|x| x.1.ok()).count(), len);
		assert_eq!(state.read().transactions.len(), 4);

		// now check that the transaction nonces are not equal
		let s = state.read();
		fn nonce(tx: UncheckedExtrinsic) -> frame_system::CheckNonce<Runtime> {
			let extra = tx.signature.unwrap().2;
			extra.4
		}
		let nonce1 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[0]).unwrap());
		let nonce2 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[1]).unwrap());
		let nonce3 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[2]).unwrap());
		let nonce4 = nonce(UncheckedExtrinsic::decode(&mut &*s.transactions[3]).unwrap());
		assert!(
			nonce1 != nonce3,
			"Transactions should have different nonces. Got: 1st tx nonce: {:?}, 2nd nonce: {:?}", nonce1, nonce3
		);
		assert!(
			nonce2 != nonce4,
			"Transactions should have different nonces. Got: 1st tx nonce: {:?}, 2nd tx nonce: {:?}", nonce2, nonce4
		);
	});
}

#[test]
fn submitted_transaction_should_be_valid() {
	use codec::Encode;
	use sp_runtime::{
		traits::StaticLookup,
		transaction_validity::{TransactionSource, TransactionTag},
	};

	let mut t = new_test_ext(compact_code_unwrap(), false);
	let (pool, state) = TestTransactionPoolExt::new();
	t.register_extension(TransactionPoolExt::new(pool));

	let keystore = KeyStore::new();
	SyncCryptoStore::sr25519_generate_new(
		&keystore,
		sr25519::AuthorityId::ID,
		Some(&format!("{}/hunter1", PHRASE)),
	)
	.unwrap();
	t.register_extension(KeystoreExt(Arc::new(keystore)));

	t.execute_with(|| {
		let results =
			Signer::<Runtime, TestAuthorityId>::all_accounts().send_signed_transaction(|_| {
				pallet_balances::Call::transfer(Default::default(), Default::default())
			});
		let len = results.len();
		assert_eq!(len, 1);
		assert_eq!(results.into_iter().filter_map(|x| x.1.ok()).count(), len);
	});

	// check that transaction is valid, but reset environment storage,
	// since CreateTransaction increments the nonce
	let tx0 = state.read().transactions[0].clone();
	let mut t = new_test_ext(compact_code_unwrap(), false);
	t.execute_with(|| {
		let source = TransactionSource::External;
		let extrinsic = UncheckedExtrinsic::decode(&mut &*tx0).unwrap();
		// add balance to the account
		let author = extrinsic.signature.clone().unwrap().0;
		let address = Indices::lookup(author).unwrap();
		let data = pallet_balances::AccountData { free: 5_000_000_000_000, ..Default::default() };
		let account = frame_system::AccountInfo { data, ..Default::default() };
		<frame_system::Account<Runtime>>::insert(&address, account);

		// check validity
		let res = Executive::validate_transaction(
			source,
			extrinsic,
			frame_system::BlockHash::<Runtime>::get(0),
		)
		.unwrap();

		// We ignore res.priority since this number can change based on updates to weights and such.
		assert_eq!(res.requires, Vec::<TransactionTag>::new());
		assert_eq!(res.provides, vec![(address, 0).encode()]);
		assert_eq!(res.longevity, 2047);
		assert_eq!(res.propagate, true);
	});
}
