// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Integration tests for ecdsa
use std::sync::Arc;
use sp_runtime::generic::BlockId;
use sp_core::{
	crypto::Pair,
	testing::ECDSA,
};
use sp_keystore::{
	SyncCryptoStore,
	testing::KeyStore,
};
use substrate_test_runtime_client::{
	TestClientBuilder, DefaultTestClientBuilderExt, TestClientBuilderExt,
	runtime::TestAPI,
};
use sp_api::ProvideRuntimeApi;
use sp_application_crypto::ecdsa::{AppPair, AppPublic};

#[test]
fn ecdsa_works_in_runtime() {
	let keystore = Arc::new(KeyStore::new());
	let test_client = TestClientBuilder::new().set_keystore(keystore.clone()).build();
	let (signature, public) = test_client.runtime_api()
		.test_ecdsa_crypto(&BlockId::Number(0))
		.expect("Tests `ecdsa` crypto.");

	let supported_keys = SyncCryptoStore::keys(&*keystore, ECDSA).unwrap();
	assert!(supported_keys.contains(&public.clone().into()));
	assert!(AppPair::verify(&signature, "ecdsa", &AppPublic::from(public)));
}
