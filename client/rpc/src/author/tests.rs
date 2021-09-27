// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use assert_matches::assert_matches;
use codec::Encode;
use jsonrpsee::{
	types::v2::{Response, RpcError, SubscriptionResponse},
	RpcModule,
};
use sc_transaction_pool::{BasicPool, FullChainApi};
use serde_json::value::to_raw_value;
use sp_core::{
	blake2_256,
	bytes::to_hex,
	crypto::{CryptoTypePublicPair, Pair, Public},
	ed25519,
	hexdisplay::HexDisplay,
	sr25519,
	testing::{ED25519, SR25519},
	H256,
};
use sp_keystore::testing::KeyStore;
use std::{mem, sync::Arc};
use substrate_test_runtime_client::{
	self,
	runtime::{Block, Extrinsic, SessionKeys, Transfer},
	AccountKeyring, Backend, Client, DefaultTestClientBuilderExt, TestClientBuilderExt,
};

fn uxt(sender: AccountKeyring, nonce: u64) -> Extrinsic {
	let tx =
		Transfer { amount: Default::default(), nonce, from: sender.into(), to: Default::default() };
	tx.into_signed_tx()
}

type FullTransactionPool = BasicPool<FullChainApi<Client<Backend>, Block>, Block>;

struct TestSetup {
	pub client: Arc<Client<Backend>>,
	pub keystore: Arc<KeyStore>,
	pub pool: Arc<FullTransactionPool>,
}

impl Default for TestSetup {
	fn default() -> Self {
		let keystore = Arc::new(KeyStore::new());
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
			executor: SubscriptionTaskExecutor::default(),
		}
	}

	fn into_rpc() -> RpcModule<Author<FullTransactionPool, Client<Backend>>> {
		Self::default().author().into_rpc()
	}
}

#[tokio::test]
async fn author_submit_transaction_should_not_cause_error() {
	env_logger::init();
	let author = TestSetup::default().author();
	let api = author.into_rpc();
	let xt: Bytes = uxt(AccountKeyring::Alice, 1).encode().into();
	let extrinsic_hash: H256 = blake2_256(&xt).into();
	let params = to_raw_value(&[xt.clone()]).unwrap();
	let json = api.call("author_submitExtrinsic", Some(params)).await.unwrap();
	let response: Response<H256> = serde_json::from_str(&json).unwrap();

	assert_eq!(response.result, extrinsic_hash,);

	// Can't submit the same extrinsic twice
	let params_again = to_raw_value(&[xt]).unwrap();
	let json = api.call("author_submitExtrinsic", Some(params_again)).await.unwrap();
	let response: RpcError = serde_json::from_str(&json).unwrap();

	assert!(response.error.message.contains("Already imported"));
}

#[tokio::test]
async fn author_should_watch_extrinsic() {
	let api = TestSetup::into_rpc();

	let xt = {
		let xt_bytes = uxt(AccountKeyring::Alice, 0).encode();
		to_raw_value(&[to_hex(&xt_bytes, true)]).unwrap()
	};

	let (subscription_id, mut rx) =
		api.test_subscription("author_submitAndWatchExtrinsic", Some(xt)).await;
	let subscription_data = rx.next().await;

	let expected = Some(format!(
		// TODO: (dp) The `jsonrpc` version of this wraps the subscription ID in `"` – is this a problem? I think not.
		r#"{{"jsonrpc":"2.0","method":"author_submitAndWatchExtrinsic","params":{{"subscription":{},"result":"ready"}}}}"#,
		subscription_id,
	));
	assert_eq!(subscription_data, expected);

	// Replace the extrinsic and observe the subscription is notified.
	let (xt_replacement, xt_hash) = {
		let tx = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		};
		let tx = tx.into_signed_tx().encode();
		let hash = blake2_256(&tx);

		(to_raw_value(&[to_hex(&tx, true)]).unwrap(), hash)
	};

	let _ = api.call("author_submitExtrinsic", Some(xt_replacement)).await.unwrap();

	let expected = Some(format!(
		// TODO: (dp) The `jsonrpc` version of this wraps the subscription ID in `"` – is this a
		// problem? I think not.
		r#"{{"jsonrpc":"2.0","method":"author_submitAndWatchExtrinsic","params":{{"subscription":{},"result":{{"usurped":"0x{}"}}}}}}"#,
		subscription_id,
		HexDisplay::from(&xt_hash),
	));
	let subscription_data = rx.next().await;
	assert_eq!(subscription_data, expected);
}

#[tokio::test]
async fn author_should_return_watch_validation_error() {
	const METH: &'static str = "author_submitAndWatchExtrinsic";

	let api = TestSetup::into_rpc();
	// Nonsensical nonce
	let invalid_xt = {
		let xt_bytes = uxt(AccountKeyring::Alice, 179).encode();
		to_raw_value(&[to_hex(&xt_bytes, true)]).unwrap()
	};
	let (_, mut data_stream) = api.test_subscription(METH, Some(invalid_xt)).await;

	let subscription_data = data_stream.next().await.unwrap();
	let response: SubscriptionResponse<String> =
		serde_json::from_str(&subscription_data).expect("subscriptions respond");
	assert!(response.params.result.contains("subscription useless"));
}

#[tokio::test]
async fn author_should_return_pending_extrinsics() {
	const METH: &'static str = "author_pendingExtrinsics";

	let api = TestSetup::into_rpc();

	let (xt, xt_bytes) = {
		let xt_bytes = uxt(AccountKeyring::Alice, 0).encode();
		let xt_hex = to_hex(&xt_bytes, true);
		(to_raw_value(&[xt_hex]).unwrap(), xt_bytes.into())
	};
	api.call("author_submitExtrinsic", Some(xt)).await.unwrap();

	let pending = api.call(METH, None).await.unwrap();
	log::debug!(target: "test", "pending: {:?}", pending);
	let pending = {
		let r: Response<Vec<Bytes>> = serde_json::from_str(&pending).unwrap();
		r.result
	};
	assert_eq!(pending, &[xt_bytes]);
}

#[tokio::test]
async fn author_should_remove_extrinsics() {
	const METH: &'static str = "author_removeExtrinsic";
	let setup = TestSetup::default();
	let api = setup.author().into_rpc();

	// Submit three extrinsics, then remove two of them (will cause the third to be removed as well,
	// having a higher nonce)
	let (xt1, xt1_bytes) = {
		let xt_bytes = uxt(AccountKeyring::Alice, 0).encode();
		let xt_hex = to_hex(&xt_bytes, true);
		(to_raw_value(&[xt_hex]).unwrap(), xt_bytes)
	};
	let xt1_out = api.call("author_submitExtrinsic", Some(xt1)).await.unwrap();
	let xt1_hash: Response<H256> = serde_json::from_str(&xt1_out).unwrap();
	let xt1_hash = xt1_hash.result;

	let (xt2, xt2_bytes) = {
		let xt_bytes = uxt(AccountKeyring::Alice, 1).encode();
		let xt_hex = to_hex(&xt_bytes, true);
		(to_raw_value(&[xt_hex]).unwrap(), xt_bytes)
	};
	let xt2_out = api.call("author_submitExtrinsic", Some(xt2)).await.unwrap();
	let xt2_hash: Response<H256> = serde_json::from_str(&xt2_out).unwrap();
	let xt2_hash = xt2_hash.result;

	let (xt3, xt3_bytes) = {
		let xt_bytes = uxt(AccountKeyring::Bob, 0).encode();
		let xt_hex = to_hex(&xt_bytes, true);
		(to_raw_value(&[xt_hex]).unwrap(), xt_bytes)
	};
	let xt3_out = api.call("author_submitExtrinsic", Some(xt3)).await.unwrap();
	let xt3_hash: Response<H256> = serde_json::from_str(&xt3_out).unwrap();
	let xt3_hash = xt3_hash.result;
	assert_eq!(setup.pool.status().ready, 3);

	// Now remove all three.
	// Notice how we need an extra `Vec` wrapping the `Vec` we want to submit as params.
	let removed = api
		.call_with(
			METH,
			vec![vec![
				hash::ExtrinsicOrHash::Hash(xt3_hash),
				// Removing this one will also remove xt2
				hash::ExtrinsicOrHash::Extrinsic(xt1_bytes.into()),
			]],
		)
		.await
		.unwrap();

	let removed: Response<Vec<H256>> = serde_json::from_str(&removed).unwrap();
	assert_eq!(removed.result, vec![xt1_hash, xt2_hash, xt3_hash]);
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
	api.call_with("author_insertKey", params).await.unwrap();
	let pubkeys = SyncCryptoStore::keys(&*setup.keystore, ED25519).unwrap();

	assert!(
		pubkeys.contains(&CryptoTypePublicPair(ed25519::CRYPTO_ID, keypair.public().to_raw_vec()))
	);
}

#[tokio::test]
async fn author_should_rotate_keys() {
	let setup = TestSetup::default();
	let api = setup.author().into_rpc();

	let new_pubkeys = {
		let json = api.call("author_rotateKeys", None).await.unwrap();
		let response: Response<Bytes> = serde_json::from_str(&json).unwrap();
		response.result
	};

	let session_keys =
		SessionKeys::decode(&mut &new_pubkeys[..]).expect("SessionKeys decode successfully");
	let ed25519_pubkeys = SyncCryptoStore::keys(&*setup.keystore, ED25519).unwrap();
	let sr25519_pubkeys = SyncCryptoStore::keys(&*setup.keystore, SR25519).unwrap();
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
	let pubkeys = {
		let json = api.call("author_rotateKeys", None).await.expect("Rotates the keys");
		let response: Response<Bytes> = serde_json::from_str(&json).unwrap();
		response.result
	};

	// Add a session key in a different keystore
	let non_existent_pubkeys = {
		let api2 = TestSetup::default().author().into_rpc();
		let json = api2.call("author_rotateKeys", None).await.expect("Rotates the keys");
		let response: Response<Bytes> = serde_json::from_str(&json).unwrap();
		response.result
	};

	// Then…
	let existing = {
		let json = api.call_with("author_hasSessionKeys", vec![pubkeys]).await.unwrap();
		let response: Response<bool> = serde_json::from_str(&json).unwrap();
		response.result
	};
	assert!(existing, "Existing key is in the session keys");

	let inexistent = {
		let json = api
			.call_with("author_hasSessionKeys", vec![non_existent_pubkeys])
			.await
			.unwrap();
		let response: Response<bool> = serde_json::from_str(&json).unwrap();
		response.result
	};
	assert_eq!(inexistent, false, "Inexistent key is not in the session keys");

	let invalid = {
		let json = api
			.call_with("author_hasSessionKeys", vec![Bytes::from(vec![1, 2, 3])])
			.await
			.unwrap();
		let response: RpcError = serde_json::from_str(&json).unwrap();
		response.error.message.to_string()
	};
	assert_eq!(invalid, "Session keys are not encoded correctly");
}

#[tokio::test]
async fn author_has_key() {
	let api = TestSetup::into_rpc();
	let suri = "//Alice";
	let alice_keypair = ed25519::Pair::from_string(suri, None).expect("Generates keypair");
	let params = (
		String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		suri.to_string(),
		Bytes::from(alice_keypair.public().0.to_vec()),
	);

	let json = api.call_with("author_insertKey", params).await.unwrap();
	serde_json::from_str::<Response<()>>(&json).expect("insertKey works");

	let bob_keypair = ed25519::Pair::from_string("//Bob", None).expect("Generates keypair");

	// Alice's ED25519 key is there
	let has_alice_ed = {
		let params = (
			Bytes::from(alice_keypair.public().to_raw_vec()),
			String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		let json = api.call_with("author_hasKey", params).await.unwrap();
		let response: Response<bool> = serde_json::from_str(&json).unwrap();
		response.result
	};
	assert!(has_alice_ed);

	// Alice's SR25519 key is not there
	let has_alice_sr = {
		let params = (
			Bytes::from(alice_keypair.public().to_raw_vec()),
			String::from_utf8(SR25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		let json = api.call_with("author_hasKey", params).await.unwrap();
		let response: Response<bool> = serde_json::from_str(&json).unwrap();
		response.result
	};
	assert!(!has_alice_sr);

	// Bob's ED25519 key is not there
	let has_bob_ed = {
		let params = (
			Bytes::from(bob_keypair.public().to_raw_vec()),
			String::from_utf8(ED25519.0.to_vec()).expect("Keytype is a valid string"),
		);
		let json = api.call_with("author_hasKey", params).await.unwrap();
		let response: Response<bool> = serde_json::from_str(&json).unwrap();
		response.result
	};
	assert!(!has_bob_ed);
}
