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

//! # Statement runtime support tests.

#![cfg(test)]

use super::*;
use crate::mock::*;
use sp_core::Pair;
use sp_runtime::AccountId32;
use sp_statement_store::{
	runtime_api::{InvalidStatement, StatementSource, ValidStatement},
	Proof, Statement,
};

#[test]
fn sign_and_validate_no_balance() {
	new_test_ext().execute_with(|| {
		let pair = sp_core::sr25519::Pair::from_string("//Bob", None).unwrap();
		let mut statement = Statement::new();
		statement.sign_sr25519_private(&pair);
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(
			Ok(ValidStatement { max_count: MIN_ALLOWED_STATEMENTS, max_size: MIN_ALLOWED_BYTES }),
			result
		);

		let pair = sp_core::ed25519::Pair::from_string("//Bob", None).unwrap();
		let mut statement = Statement::new();
		statement.sign_ed25519_private(&pair);
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(
			Ok(ValidStatement { max_count: MIN_ALLOWED_STATEMENTS, max_size: MIN_ALLOWED_BYTES }),
			result
		);

		let pair = sp_core::ecdsa::Pair::from_string("//Bob", None).unwrap();
		let mut statement = Statement::new();
		statement.sign_ecdsa_private(&pair);
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(
			Ok(ValidStatement { max_count: MIN_ALLOWED_STATEMENTS, max_size: MIN_ALLOWED_BYTES }),
			result
		);
	});
}

#[test]
fn validate_with_balance() {
	new_test_ext().execute_with(|| {
		let pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let mut statement = Statement::new();
		statement.sign_sr25519_private(&pair);
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(Ok(ValidStatement { max_count: 6, max_size: 3000 }), result);

		let pair = sp_core::sr25519::Pair::from_string("//Charlie", None).unwrap();
		let mut statement = Statement::new();
		statement.sign_sr25519_private(&pair);
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(
			Ok(ValidStatement { max_count: MAX_ALLOWED_STATEMENTS, max_size: MAX_ALLOWED_BYTES }),
			result
		);
	});
}

#[test]
fn validate_no_proof_fails() {
	new_test_ext().execute_with(|| {
		let statement = Statement::new();
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(Err(InvalidStatement::NoProof), result);
	});
}

#[test]
fn validate_bad_signature_fails() {
	new_test_ext().execute_with(|| {
		let statement = Statement::new_with_proof(Proof::Sr25519 {
			signature: [0u8; 64],
			signer: Default::default(),
		});
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(Err(InvalidStatement::BadProof), result);
	});
}

#[test]
fn validate_event() {
	new_test_ext().execute_with(|| {
		let parent_hash = sp_core::H256::random();
		System::reset_events();
		System::initialize(&1, &parent_hash, &Default::default());
		let mut statement = Statement::new();
		let pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let account: AccountId32 = pair.public().into();
		Pallet::<Test>::submit_statement(account.clone(), statement.clone());
		statement.set_proof(Proof::OnChain {
			who: account.clone().into(),
			event_index: 0,
			block_hash: parent_hash.into(),
		});
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement.clone());
		assert_eq!(Ok(ValidStatement { max_count: 6, max_size: 3000 }), result);

		// Use wrong event index
		statement.set_proof(Proof::OnChain {
			who: account.clone().into(),
			event_index: 1,
			block_hash: parent_hash.into(),
		});
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement.clone());
		assert_eq!(Err(InvalidStatement::BadProof), result);

		// Use wrong block hash
		statement.set_proof(Proof::OnChain {
			who: account.clone().into(),
			event_index: 0,
			block_hash: sp_core::H256::random().into(),
		});
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement.clone());
		assert_eq!(Err(InvalidStatement::BadProof), result);
	});
}

#[test]
fn validate_no_event_fails() {
	new_test_ext().execute_with(|| {
		let parent_hash = sp_core::H256::random();
		System::reset_events();
		System::initialize(&1, &parent_hash, &Default::default());
		let mut statement = Statement::new();
		let pair = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let account: AccountId32 = pair.public().into();
		statement.set_proof(Proof::OnChain {
			who: account.into(),
			event_index: 0,
			block_hash: parent_hash.into(),
		});
		let result = Pallet::<Test>::validate_statement(StatementSource::Chain, statement);
		assert_eq!(Err(InvalidStatement::BadProof), result);
	});
}
