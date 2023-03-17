// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;

use crate::testing::{test_executor, timeout_secs};
use assert_matches::assert_matches;
use codec::Encode;
use jsonrpsee::{
	core::Error as RpcError,
	types::{error::CallError, EmptyServerParams as EmptyParams},
	RpcModule,
};
use sc_transaction_pool::{BasicPool, FullChainApi};
use sc_transaction_pool_api::TransactionStatus;
use sp_core::{
	blake2_256,
	bytes::to_hex,
	crypto::{ByteArray, CryptoTypePublicPair, Pair},
	ed25519, sr25519,
	testing::{ED25519, SR25519},
	H256,
};
use sp_keystore::testing::MemoryKeystore;
use std::sync::Arc;
use substrate_test_runtime_client::{
	self,
	runtime::{Block, Extrinsic, SessionKeys, Transfer},
	AccountKeyring, Backend, Client, DefaultTestClientBuilderExt, TestClientBuilderExt,
};

fn uxt(sender: AccountKeyring, nonce: u64) -> Extrinsic {
	let tx = Transfer {
		amount: Default::default(),
		nonce,
		from: sender.into(),
		to: AccountKeyring::Bob.into(),
	};
	tx.into_signed_tx()
}

type FullTransactionPool = BasicPool<FullChainApi<Client<Backend>, Block>, Block>;

struct TestSetup {
	pub client: Arc<Client<Backend>>,
	pub keystore: Arc<MemoryKeystore>,
	pub pool: Arc<FullTransactionPool>,
}

impl Default for TestSetup {
	fn default() -> Self {
		let keystore = Arc::new(MemoryKeystore::new());
		let client_builder = substrate_test_runtime_client::TestClientBuilder::new();
		let client = Arc::new(client_builder.set_keystore(keystore.clone()).build());

		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());
		TestSetup { client, keystore, pool }
	}
}

impl TestSetup {
	fn author(&self) -> Author<FullTransactionPool, Client<Backend>> {
		Author {
			client: self.client.clone(),
			pool: self.pool.clone(),
			keystore: self.keystore.clone(),
			deny_unsafe: DenyUnsafe::No,
			executor: test_executor(),
		}
	}

	fn into_rpc() -> RpcModule<Author<FullTransactionPool, Client<Backend>>> {
		Self::default().author().into_rpc()
	}
}

#[tokio::test]
async fn author_submit_transaction_should_not_cause_error() {
	let _ = env_logger::try_init();
	let author = TestSetup::default().author();
	let api = author.into_rpc();
	let xt: Bytes = uxt(AccountKeyring::Alice, 1).encode().into();
	let extrinsic_hash: H256 = blake2_256(&xt).into();
	let response: H256 = api.call("author_submitExtrinsic", [xt.clone()]).await.unwrap();

	assert_eq!(response, extrinsic_hash);

	assert_matches!(
		api.call::<_, H256>("author_submitExtrinsic", [xt]).await,
		Err(RpcError::Call(CallError::Custom(err))) if err.message().contains("Already Imported") && err.code() == 1013
	);
}

#[tokio::test]
async fn author_should_watch_extrinsic() {
	let api = TestSetup::into_rpc();
	let xt = to_hex(&uxt(AccountKeyring::Alice, 0).encode(), true);

	let mut sub = api.subscribe("author_submitAndWatchExtrinsic", [xt]).await.unwrap();
	let (tx, sub_id) = timeout_secs(10, sub.next::<TransactionStatus<H256, Block>>())
		.await
		.unwrap()
		.unwrap()
		.unwrap();

	assert_matches!(tx, TransactionStatus::Ready);
	assert_eq!(&sub_id, sub.subscription_id());

	// Replace the extrinsic and observe the subscription is notified.
	let (xt_replacement, xt_hash) = {
		let tx = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
		};
		let tx = tx.into_signed_tx().encode();
		let hash = blake2_256(&tx);

		(to_hex(&tx, true), hash)
	};

	let _ = api.call::<_, H256>("author_submitExtrinsic", [xt_replacement]).await.unwrap();

	let (tx, sub_id) = timeout_secs(10, sub.next::<TransactionStatus<H256, Block>>())
		.await
		.unwrap()
		.unwrap()
		.unwrap();
	assert_eq!(tx, TransactionStatus::Usurped(xt_hash.into()));
	assert_eq!(&sub_id, sub.subscription_id());
}

#[tokio::test]
async fn author_should_return_watch_validation_error() {
	const METHOD: &'static str = "author_submitAndWatchExtrinsic";

	let api = TestSetup::into_rpc();
	let failed_sub = api
		.subscribe(METHOD, [to_hex(&uxt(AccountKeyring::Alice, 179).encode(), true)])
		.await;

	assert_matches!(
		failed_sub,
		Err(RpcError::Call(CallError::Custom(err))) if err.message().contains("Invalid Transaction") && err.code() == 1010
	);
}

#[tokio::test]
async fn author_should_return_pending_extrinsics() {
	let api = TestSetup::into_rpc();

	let xt_bytes: Bytes = uxt(AccountKeyring::Alice, 0).encode().into();
	api.call::<_, H256>("author_submitExtrinsic", [to_hex(&xt_bytes, true)])
		.await
		.unwrap();

	let pending: Vec<Bytes> =
		api.call("author_pendingExtrinsics", EmptyParams::new()).await.unwrap();
	assert_eq!(pending, vec![xt_bytes]);
}

#[tokio::test]
async fn author_should_remove_extrinsics() {
	const METHOD: &'static str = "author_removeExtrinsic";
	let setup = TestSetup::default();
	let api = setup.author().into_rpc();

	// Submit three extrinsics, then remove two of them (will cause the third to be removed as well,
	// having a higher nonce)
	let xt1_bytes = uxt(AccountKeyring::Alice, 0).encode();
	let xt1 = to_hex(&xt1_bytes, true);
	let xt1_hash: H256 = api.call("author_submitExtrinsic", [xt1]).await.unwrap();

	let xt2 = to_hex(&uxt(AccountKeyring::Alice, 1).encode(), true);
	let xt2_hash: H256 = api.call("author_submitExtrinsic", [xt2]).await.unwrap();

	let xt3 = to_hex(&uxt(AccountKeyring::Bob, 0).encode(), true);
	let xt3_hash: H256 = api.call("author_submitExtrinsic", [xt3]).await.unwrap();
	assert_eq!(setup.pool.status().ready, 3);

	// Now remove all three.
	// Notice how we need an extra `Vec` wrapping the `Vec` we want to submit as params.
	let removed: Vec<H256> = api
		.call(
			METHOD,
			vec![vec![
				hash::ExtrinsicOrHash::Hash(xt3_hash),
				// Removing this one will also remove xt2
				hash::ExtrinsicOrHash::Extrinsic(xt1_bytes.into()),
			]],
		)
		.await
		.unwrap();

	assert_eq!(removed, vec![xt1_hash, xt2_hash, xt3_hash]);
}

#[tokio::test]
async fn author_should_insert_key() {
	let setup = TestSetup::default();
	let api = setup.author().into_rpc();
	let suri = "//Alice";
	let keypair = ed25519::Pair::from_string(suri, None).expect("generates keypair");
	let params: (String, String, Bytes) = (
		String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		suri.to_string(),
		keypair.public().0.to_vec().into(),
	);
	api.call::<_, ()>("author_insertKey", params).await.unwrap();
	let pubkeys = Keystore::keys(&*setup.keystore, ED25519).unwrap();

	assert!(
		pubkeys.contains(&CryptoTypePublicPair(ed25519::CRYPTO_ID, keypair.public().to_raw_vec()))
	);
}

#[tokio::test]
async fn author_should_rotate_keys() {
	let setup = TestSetup::default();
	let api = setup.author().into_rpc();

	let new_pubkeys: Bytes = api.call("author_rotateKeys", EmptyParams::new()).await.unwrap();
	let session_keys =
		SessionKeys::decode(&mut &new_pubkeys[..]).expect("SessionKeys decode successfully");
	let ed25519_pubkeys = Keystore::keys(&*setup.keystore, ED25519).unwrap();
	let sr25519_pubkeys = Keystore::keys(&*setup.keystore, SR25519).unwrap();
	assert!(ed25519_pubkeys
		.contains(&CryptoTypePublicPair(ed25519::CRYPTO_ID, session_keys.ed25519.to_raw_vec())));
	assert!(sr25519_pubkeys
		.contains(&CryptoTypePublicPair(sr25519::CRYPTO_ID, session_keys.sr25519.to_raw_vec())));
}

#[tokio::test]
async fn author_has_session_keys() {
	// Setup
	let api = TestSetup::into_rpc();

	// Add a valid session key
	let pubkeys: Bytes = api
		.call("author_rotateKeys", EmptyParams::new())
		.await
		.expect("Rotates the keys");

	// Add a session key in a different keystore
	let non_existent_pubkeys: Bytes = {
		let api2 = TestSetup::default().author().into_rpc();
		api2.call("author_rotateKeys", EmptyParams::new())
			.await
			.expect("Rotates the keys")
	};

	// Then…
	let existing = api.call::<_, bool>("author_hasSessionKeys", vec![pubkeys]).await.unwrap();
	assert!(existing, "Existing key is in the session keys");

	let inexistent = api
		.call::<_, bool>("author_hasSessionKeys", vec![non_existent_pubkeys])
		.await
		.unwrap();
	assert_eq!(inexistent, false, "Inexistent key is not in the session keys");

	assert_matches!(
		api.call::<_, bool>("author_hasSessionKeys", vec![Bytes::from(vec![1, 2, 3])]).await,
		Err(RpcError::Call(CallError::Custom(err))) if err.message().contains("Session keys are not encoded correctly")
	);
}

#[tokio::test]
async fn author_has_key() {
	let _ = env_logger::try_init();

	let api = TestSetup::into_rpc();
	let suri = "//Alice";
	let alice_keypair = ed25519::Pair::from_string(suri, None).expect("Generates keypair");
	let params = (
		String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		suri.to_string(),
		Bytes::from(alice_keypair.public().0.to_vec()),
	);

	api.call::<_, ()>("author_insertKey", params).await.expect("insertKey works");

	let bob_keypair = ed25519::Pair::from_string("//Bob", None).expect("Generates keypair");

	// Alice's ED25519 key is there
	let has_alice_ed: bool = {
		let params = (
			Bytes::from(alice_keypair.public().to_raw_vec()),
			String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		api.call("author_hasKey", params).await.unwrap()
	};
	assert!(has_alice_ed);

	// Alice's SR25519 key is not there
	let has_alice_sr: bool = {
		let params = (
			Bytes::from(alice_keypair.public().to_raw_vec()),
			String::from_utf8(SR25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		api.call("author_hasKey", params).await.unwrap()
	};
	assert!(!has_alice_sr);

	// Bob's ED25519 key is not there
	let has_bob_ed: bool = {
		let params = (
			Bytes::from(bob_keypair.public().to_raw_vec()),
			String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		api.call("author_hasKey", params).await.unwrap()
	};
	assert!(!has_bob_ed);
}
