// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Integration tests for ed25519

use sp_api::ProvideRuntimeApi;
use sp_application_crypto::ed25519::{AppPair, AppPublic};
use sp_core::{crypto::Pair, testing::ED25519};
use sp_keystore::{testing::KeyStore, SyncCryptoStore};
use std::sync::Arc;
use substrate_test_runtime_client::{
	runtime::TestAPI, DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
};

#[test]
fn ed25519_works_in_runtime() {
	let keystore = Arc::new(KeyStore::new());
	let test_client = TestClientBuilder::new().set_keystore(keystore.clone()).build();
	let (signature, public) = test_client
		.runtime_api()
		.test_ed25519_crypto(test_client.chain_info().genesis_hash)
		.expect("Tests `ed25519` crypto.");

	let supported_keys = SyncCryptoStore::keys(&*keystore, ED25519).unwrap();
	assert!(supported_keys.contains(&public.clone().into()));
	assert!(AppPair::verify(&signature, "ed25519", &AppPublic::from(public)));
}
