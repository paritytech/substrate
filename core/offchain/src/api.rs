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

use std::sync::Arc;
use client::backend::OffchainStorage;
use crate::AuthorityKeyProvider;
use futures::{Stream, Future, sync::mpsc};
use log::{info, debug, warn, error};
use parity_codec::{Encode, Decode};
use primitives::offchain::{
	Timestamp, HttpRequestId, HttpRequestStatus, HttpError,
	Externalities as OffchainExt,
	CryptoKind, CryptoKeyId,
	StorageKind,
};
use primitives::crypto::{Pair, Protected};
use primitives::{ed25519, sr25519};
use runtime_primitives::{
	generic::BlockId,
	traits::{self, Extrinsic},
};
use transaction_pool::txpool::{Pool, ChainApi};

/// A message between the offchain extension and the processing thread.
enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

/// A persisted key seed.
#[derive(Encode, Decode)]
struct CryptoKey {
	kind: CryptoKind,
	phrase: String,
}

enum Key {
	Sr25519(sr25519::Pair),
	Ed25519(ed25519::Pair),
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct Api<Storage, KeyProvider> {
	sender: mpsc::UnboundedSender<ExtMessage>,
	db: Storage,
	keys_password: Protected<String>,
	key_provider: KeyProvider,
}

fn unavailable_yet<R: Default>(name: &str) -> R {
	error!("The {:?} API is not available for offchain workers yet. Follow \
		   https://github.com/paritytech/substrate/issues/1458 for details", name);
	Default::default()
}

const LOCAL_DB: &str = "LOCAL (fork-aware) DB";
const STORAGE_PREFIX: &[u8] = b"storage";
const KEYS_PREFIX: &[u8] = b"keys";

const NEXT_ID: &[u8] = b"crypto_key_id";

impl<Storage, KeyProvider> Api<Storage, KeyProvider> where
	Storage: OffchainStorage,
	KeyProvider: AuthorityKeyProvider,
{
	fn keypair<P: Pair>(&self, phrase: &str) -> Result<P, ()> {
		P::from_phrase(phrase, Some(self.keys_password.as_ref()))
			.map_err(|e| {
				warn!("Error recovering Offchain Worker key. Password invalid? {:?}", e);
				()
			})
			.map(|x| x.0)
	}

	fn read_key(&self, id: Option<CryptoKeyId>, kind: CryptoKind) -> Result<Key, ()> {
		if let Some(id) = id {
			let key = self.db.get(KEYS_PREFIX, &id.0.encode())
				.and_then(|key| CryptoKey::decode(&mut &*key))
				.ok_or(())?;
			if key.kind != kind {
				warn!(
					"Invalid crypto kind (got: {:?}, expected: {:?}), when requesting key {:?}",
					key.kind,
					kind,
					id
				);
				return Err(())
			}

			Ok(match key.kind {
				CryptoKind::Sr25519 => Key::Sr25519(self.keypair(&key.phrase)?),
				CryptoKind::Ed25519 => Key::Ed25519(self.keypair(&key.phrase)?),
			})
		} else {
			let key = match kind {
				CryptoKind::Sr25519 => self.key_provider.authority_key().map(Key::Sr25519),
				CryptoKind::Ed25519 => self.key_provider.authority_key().map(Key::Ed25519),
			};

			key.ok_or_else(|| {
				warn!("AuthorityKey is not configured, yet offchain worker tried to access it.");
				()
			})
		}
	}
}

impl<Storage, KeyProvider> OffchainExt for Api<Storage, KeyProvider> where
	Storage: OffchainStorage,
	KeyProvider: AuthorityKeyProvider,
{
	fn submit_transaction(&mut self, ext: Vec<u8>) -> Result<(), ()> {
		self.sender
			.unbounded_send(ExtMessage::SubmitExtrinsic(ext))
			.map(|_| ())
			.map_err(|_| ())
	}

	fn new_crypto_key(&mut self, kind: CryptoKind) -> Result<CryptoKeyId, ()> {
		let phrase = match kind {
			CryptoKind::Ed25519 => {
				ed25519::Pair::generate_with_phrase(Some(self.keys_password.as_ref())).1
			},
			CryptoKind::Sr25519 => {
				sr25519::Pair::generate_with_phrase(Some(self.keys_password.as_ref())).1
			},
		};

		let (id, id_encoded) = loop {
			let encoded = self.db.get(KEYS_PREFIX, NEXT_ID);
			let encoded_slice = encoded.as_ref().map(|x| x.as_slice());
			let new_id = encoded_slice.and_then(|mut x| u16::decode(&mut x)).unwrap_or_default()
				.checked_add(1)
				.ok_or(())?;
			let new_id_encoded = new_id.encode();

			if self.db.compare_and_set(KEYS_PREFIX, NEXT_ID, encoded_slice, &new_id_encoded) {
				break (new_id, new_id_encoded);
			}
		};

		self.db.set(KEYS_PREFIX, &id_encoded, &CryptoKey { phrase, kind } .encode());

		Ok(CryptoKeyId(id))
	}

	fn encrypt(&mut self, _key: Option<CryptoKeyId>, _kind: CryptoKind, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("encrypt");
		Err(())
	}

	fn decrypt(&mut self, _key: Option<CryptoKeyId>, _kind: CryptoKind, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("decrypt");
		Err(())

	}

	fn sign(&mut self, key: Option<CryptoKeyId>, kind: CryptoKind, data: &[u8]) -> Result<Vec<u8>, ()> {
		let key = self.read_key(key, kind)?;

		Ok(match key {
			Key::Sr25519(pair) => pair.sign(data).0.to_vec(),
			Key::Ed25519(pair) => pair.sign(data).0.to_vec(),
		})
	}

	fn verify(&mut self, key: Option<CryptoKeyId>, kind: CryptoKind, msg: &[u8], signature: &[u8]) -> Result<bool, ()> {
		let key = self.read_key(key, kind)?;

		Ok(match key {
			Key::Sr25519(pair) => sr25519::Pair::verify_weak(signature, msg, pair.public()),
			Key::Ed25519(pair) => ed25519::Pair::verify_weak(signature, msg, pair.public()),
		})
	}

	fn timestamp(&mut self) -> Timestamp {
		unavailable_yet("timestamp")
	}

	fn sleep_until(&mut self, _deadline: Timestamp) {
		unavailable_yet::<()>("sleep_until")
	}

	fn random_seed(&mut self) -> [u8; 32] {
		unavailable_yet("random_seed")
	}

	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		match kind {
			StorageKind::PERSISTENT => self.db.set(STORAGE_PREFIX, key, value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_compare_and_set(
		&mut self,
		kind: StorageKind,
		key: &[u8],
		old_value: &[u8],
		new_value: &[u8],
	) -> bool {
		match kind {
			StorageKind::PERSISTENT => {
				self.db.compare_and_set(STORAGE_PREFIX, key, Some(old_value), new_value)
			},
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		match kind {
			StorageKind::PERSISTENT => self.db.get(STORAGE_PREFIX, key),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn http_request_start(
		&mut self,
		_method: &str,
		_uri: &str,
		_meta: &[u8]
	) -> Result<HttpRequestId, ()> {
		unavailable_yet::<()>("http_request_start");
		Err(())
	}

	fn http_request_add_header(
		&mut self,
		_request_id: HttpRequestId,
		_name: &str,
		_value: &str
	) -> Result<(), ()> {
		unavailable_yet::<()>("http_request_add_header");
		Err(())
	}

	fn http_request_write_body(
		&mut self,
		_request_id: HttpRequestId,
		_chunk: &[u8],
		_deadline: Option<Timestamp>
	) -> Result<(), HttpError> {
		unavailable_yet::<()>("http_request_write_body");
		Err(HttpError::IoError)
	}

	fn http_response_wait(
		&mut self,
		ids: &[HttpRequestId],
		_deadline: Option<Timestamp>
	) -> Vec<HttpRequestStatus> {
		unavailable_yet::<()>("http_response_wait");
		ids.iter().map(|_| HttpRequestStatus::Unknown).collect()
	}

	fn http_response_headers(
		&mut self,
		_request_id: HttpRequestId
	) -> Vec<(Vec<u8>, Vec<u8>)> {
		unavailable_yet("http_response_headers")
	}

	fn http_response_read_body(
		&mut self,
		_request_id: HttpRequestId,
		_buffer: &mut [u8],
		_deadline: Option<Timestamp>
	) -> Result<usize, HttpError> {
		unavailable_yet::<()>("http_response_read_body");
		Err(HttpError::IoError)
	}
}

/// Offchain extensions implementation API
///
/// This is the asynchronous processing part of the API.
pub(crate) struct AsyncApi<A: ChainApi> {
	receiver: Option<mpsc::UnboundedReceiver<ExtMessage>>,
	transaction_pool: Arc<Pool<A>>,
	at: BlockId<A::Block>,
}

impl<A: ChainApi> AsyncApi<A> {
	/// Creates new Offchain extensions API implementation  an the asynchronous processing part.
	pub fn new<S: OffchainStorage, P: AuthorityKeyProvider>(
		transaction_pool: Arc<Pool<A>>,
		db: S,
		keys_password: Protected<String>,
		key_provider: P,
		at: BlockId<A::Block>,
	) -> (Api<S, P>, AsyncApi<A>) {
		let (sender, rx) = mpsc::unbounded();

		let api = Api {
			sender,
			db,
			keys_password,
			key_provider,
		};

		let async_api = AsyncApi {
			receiver: Some(rx),
			transaction_pool,
			at,
		};

		(api, async_api)
	}

	/// Run a processing task for the API
	pub fn process(mut self) -> impl Future<Item=(), Error=()> {
		let receiver = self.receiver.take().expect("Take invoked only once.");

		receiver.for_each(move |msg| {
			match msg {
				ExtMessage::SubmitExtrinsic(ext) => self.submit_extrinsic(ext),
			}
			Ok(())
		})
	}

	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let xt = match <A::Block as traits::Block>::Extrinsic::decode(&mut &*ext) {
			Some(xt) => xt,
			None => {
				warn!("Unable to decode extrinsic: {:?}", ext);
				return
			},
		};

		info!("Submitting to the pool: {:?} (isSigned: {:?})", xt, xt.is_signed());
		match self.transaction_pool.submit_one(&self.at, xt.clone()) {
			Ok(hash) => debug!("[{:?}] Offchain transaction added to the pool.", hash),
			Err(e) => {
				debug!("Couldn't submit transaction: {:?}", e);
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use client_db::offchain::LocalStorage;
	use crate::tests::TestProvider;

	fn offchain_api() -> (Api<LocalStorage, TestProvider>, AsyncApi<impl ChainApi>) {
		let _ = env_logger::try_init();
		let db = LocalStorage::new_test();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(
			Pool::new(Default::default(), transaction_pool::ChainApi::new(client.clone()))
		);

		AsyncApi::new(pool, db, "pass".to_owned().into(), TestProvider::default(), BlockId::Number(0))
	}

	#[test]
	fn should_set_and_get_local_storage() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";

		// when
		assert_eq!(api.local_storage_get(kind, key), None);
		api.local_storage_set(kind, key, b"value");

		// then
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));
	}

	#[test]
	fn should_compare_and_set_local_storage() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";
		api.local_storage_set(kind, key, b"value");

		// when
		assert_eq!(api.local_storage_compare_and_set(kind, key, b"val", b"xxx"), false);
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));

		// when
		assert_eq!(api.local_storage_compare_and_set(kind, key, b"value", b"xxx"), true);
		assert_eq!(api.local_storage_get(kind, key), Some(b"xxx".to_vec()));
	}

	#[test]
	fn should_create_a_new_key_and_sign_and_verify_stuff() {
		let test = |kind: CryptoKind| {
			// given
			let mut api = offchain_api().0;
			let msg = b"Hello world!";

			// when
			let key_id = api.new_crypto_key(kind).unwrap();
			let signature = api.sign(Some(key_id), kind, msg).unwrap();

			// then
			let res = api.verify(Some(key_id), kind, msg, &signature).unwrap();
			assert_eq!(res, true);
			let res = api.verify(Some(key_id), kind, msg, &[]).unwrap();
			assert_eq!(res, false);
			let res = api.verify(Some(key_id), kind, b"Different msg", &signature).unwrap();
			assert_eq!(res, false);

			assert_eq!(
				api.verify(Some(key_id), CryptoKind::Sr25519, msg, &signature).is_err(),
				kind != CryptoKind::Sr25519
			);

		};

		test(CryptoKind::Ed25519);
		test(CryptoKind::Sr25519);
	}

	#[test]
	fn should_sign_and_verify_with_authority_key() {
		// given
		let mut api = offchain_api().0;
		api.key_provider.ed_key = Some(ed25519::Pair::generate().0);
		let msg = b"Hello world!";
		let kind = CryptoKind::Ed25519;

		// when
		let signature = api.sign(None, kind, msg).unwrap();

		// then
		let res = api.verify(None, kind, msg, &signature).unwrap();
		assert_eq!(res, true);
		let res = api.verify(None, kind, msg, &[]).unwrap();
		assert_eq!(res, false);
		let res = api.verify(None, kind, b"Different msg", &signature).unwrap();
		assert_eq!(res, false);

		assert!(
			api.verify(None, CryptoKind::Sr25519, msg, &signature).is_err(),
			"Invalid kind should trigger a missing key error."
		);
	}
}
