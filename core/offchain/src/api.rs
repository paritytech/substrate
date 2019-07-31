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

use std::{
	str::FromStr,
	sync::Arc,
	convert::{TryFrom, TryInto},
	time::{SystemTime, Duration},
	thread::sleep,
};
use client::backend::OffchainStorage;
use crate::AuthorityKeyProvider;
use futures::{Stream, Future, sync::mpsc};
use log::{info, debug, warn, error};
use parity_codec::{Encode, Decode};
use primitives::offchain::{
	Timestamp,
	HttpRequestId, HttpRequestStatus, HttpError,
	Externalities as OffchainExt,
	CryptoKind, CryptoKey,
	StorageKind,
	OpaqueNetworkState, OpaquePeerId, OpaqueMultiaddr,
};
use primitives::crypto::{Pair, Public, Protected};
use primitives::{ed25519, sr25519};
use sr_primitives::{
	generic::BlockId,
	traits::{self, Extrinsic},
};
use transaction_pool::txpool::{Pool, ChainApi};
use network::NetworkStateInfo;
use network::{PeerId, Multiaddr};

/// A message between the offchain extension and the processing thread.
enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

/// A persisted key seed.
#[derive(Encode, Decode)]
struct StoredKey {
	kind: CryptoKind,
	phrase: String,
}

impl StoredKey {
	fn generate_with_phrase(kind: CryptoKind, password: Option<&str>) -> Self {
		match kind {
			CryptoKind::Ed25519 => {
				let phrase = ed25519::Pair::generate_with_phrase(password).1;
				Self { kind, phrase }
			}
			CryptoKind::Sr25519 => {
				let phrase = sr25519::Pair::generate_with_phrase(password).1;
				Self { kind, phrase }
			}
		}
	}

	fn to_local_key(&self, password: Option<&str>) -> Result<LocalKey, ()> {
		match self.kind {
			CryptoKind::Ed25519 => {
				ed25519::Pair::from_phrase(&self.phrase, password)
					.map(|x| LocalKey::Ed25519(x.0))
			}
			CryptoKind::Sr25519 => {
				sr25519::Pair::from_phrase(&self.phrase, password)
					.map(|x| LocalKey::Sr25519(x.0))
			}
		}
		.map_err(|e| {
			warn!("Error recovering Offchain Worker key. Password invalid? {:?}", e);
			()
		})
	}
}

enum LocalKey {
	Ed25519(ed25519::Pair),
	Sr25519(sr25519::Pair),
}

impl LocalKey {
	fn public(&self) -> Result<Vec<u8>, ()> {
		match self {
			LocalKey::Ed25519(pair) => Ok(pair.public().to_raw_vec()),
			LocalKey::Sr25519(pair) => Ok(pair.public().to_raw_vec()),
		}
	}

	fn sign(&self, data: &[u8]) -> Result<Vec<u8>, ()> {
		match self {
			LocalKey::Ed25519(pair) => {
				let sig = pair.sign(data);
				let bytes: &[u8] = sig.as_ref();
				Ok(bytes.to_vec())
			}
			LocalKey::Sr25519(pair) => {
				let sig = pair.sign(data);
				let bytes: &[u8] = sig.as_ref();
				Ok(bytes.to_vec())
			}
		}
	}

	fn verify(&self, msg: &[u8], signature: &[u8]) -> Result<bool, ()> {
		match self {
			LocalKey::Ed25519(pair) => {
				Ok(ed25519::Pair::verify_weak(signature, msg, pair.public()))
			}
			LocalKey::Sr25519(pair) => {
				Ok(sr25519::Pair::verify_weak(signature, msg, pair.public()))
			}
		}
	}
}

/// A key.
enum Key<ConsensusPair, FinalityPair> {
	LocalKey(LocalKey),
	AuthorityKey(ConsensusPair),
	FgAuthorityKey(FinalityPair),
}

impl<ConsensusPair: Pair, FinalityPair: Pair> Key<ConsensusPair, FinalityPair> {
	fn public(&self) -> Result<Vec<u8>, ()> {
		match self {
			Key::LocalKey(local) => {
				local.public()
			}
			Key::AuthorityKey(pair) => {
				Ok(pair.public().to_raw_vec())
			}
			Key::FgAuthorityKey(pair) => {
				Ok(pair.public().to_raw_vec())
			}
		}
	}

	fn sign(&self, data: &[u8]) -> Result<Vec<u8>, ()> {
		match self {
			Key::LocalKey(local) => {
				local.sign(data)
			}
			Key::AuthorityKey(pair) => {
				Ok(pair.sign(data).as_ref().to_vec())
			}
			Key::FgAuthorityKey(pair) => {
				Ok(pair.sign(data).as_ref().to_vec())
			}
		}
	}

	fn verify(&self, msg: &[u8], signature: &[u8]) -> Result<bool, ()> {
		match self {
			Key::LocalKey(local) => {
				local.verify(msg, signature)
			}
			Key::AuthorityKey(pair) => {
				Ok(ConsensusPair::verify_weak(signature, msg, pair.public()))
			}
			Key::FgAuthorityKey(pair) => {
				Ok(FinalityPair::verify_weak(signature, msg, pair.public()))
			}
		}
	}
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct Api<Storage, KeyProvider, Block: traits::Block> {
	sender: mpsc::UnboundedSender<ExtMessage>,
	db: Storage,
	keys_password: Protected<String>,
	key_provider: KeyProvider,
	network_state: Arc<dyn NetworkStateInfo + Send + Sync>,
	at: BlockId<Block>,
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

impl<Storage, KeyProvider, Block> Api<Storage, KeyProvider, Block> where
	Storage: OffchainStorage,
	KeyProvider: AuthorityKeyProvider<Block>,
	Block: traits::Block,
{
	fn password(&self) -> Option<&str> {
		Some(self.keys_password.as_ref().as_str())
	}

	fn read_key(
		&self,
		key: CryptoKey,
	) -> Result<Key<KeyProvider::ConsensusPair, KeyProvider::FinalityPair>, ()> {
		match key {
			CryptoKey::LocalKey { id, kind } => {
				let key = self.db.get(KEYS_PREFIX, &id.encode())
					.and_then(|key| StoredKey::decode(&mut &*key))
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
				Ok(Key::LocalKey(key.to_local_key(self.password())?))
			}
			CryptoKey::AuthorityKey => {
				let key = self.key_provider
					.authority_key(&self.at)
					.ok_or(())?;
				Ok(Key::AuthorityKey(key))
			}
			CryptoKey::FgAuthorityKey => {
				let key = self.key_provider
					.fg_authority_key(&self.at)
					.ok_or(())?;
				Ok(Key::FgAuthorityKey(key))
			}
		}
	}
}

impl<Storage, KeyProvider, Block> OffchainExt for Api<Storage, KeyProvider, Block>
where
	Storage: OffchainStorage,
	KeyProvider: AuthorityKeyProvider<Block>,
	Block: traits::Block,
{
	fn submit_transaction(&mut self, ext: Vec<u8>) -> Result<(), ()> {
		self.sender
			.unbounded_send(ExtMessage::SubmitExtrinsic(ext))
			.map(|_| ())
			.map_err(|_| ())
	}

	fn new_crypto_key(&mut self, kind: CryptoKind) -> Result<CryptoKey, ()> {
		let key = StoredKey::generate_with_phrase(kind, self.password());
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

		self.db.set(KEYS_PREFIX, &id_encoded, &key.encode());

		Ok(CryptoKey::LocalKey { id, kind })
	}

	fn pubkey(&self, key: CryptoKey) -> Result<Vec<u8>, ()> {
		self.read_key(key)?.public()
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		let external_addresses = self.network_state.external_addresses();

		let state = NetworkState::new(
			self.network_state.peer_id(),
			external_addresses,
		);
		Ok(OpaqueNetworkState::from(state))
	}

	fn encrypt(&mut self, _key: CryptoKey, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("encrypt");
		Err(())
	}

	fn decrypt(&mut self, _key: CryptoKey, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("decrypt");
		Err(())

	}

	fn sign(&mut self, key: CryptoKey, data: &[u8]) -> Result<Vec<u8>, ()> {
		self.read_key(key)?.sign(data)
	}

	fn verify(&mut self, key: CryptoKey, msg: &[u8], signature: &[u8]) -> Result<bool, ()> {
		self.read_key(key)?.verify(msg, signature)
	}

	fn timestamp(&mut self) -> Timestamp {
		let now = SystemTime::now();
		let epoch_duration = now.duration_since(SystemTime::UNIX_EPOCH);
		match epoch_duration {
			Err(_) => {
				// Current time is earlier than UNIX_EPOCH.
				Timestamp::from_unix_millis(0)
			},
			Ok(d) => {
				let duration = d.as_millis();
				// Assuming overflow won't happen for a few hundred years.
				Timestamp::from_unix_millis(duration.try_into()
					.expect("epoch milliseconds won't overflow u64 for hundreds of years; qed"))
			}
		}
	}

	fn sleep_until(&mut self, deadline: Timestamp) {
		// Get current timestamp.
		let now = self.timestamp();
		// Calculate the diff with the deadline.
		let diff = deadline.diff(&now);
		// Call thread::sleep for the diff duration.
		sleep(Duration::from_millis(diff.millis()));
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
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		match kind {
			StorageKind::PERSISTENT => {
				self.db.compare_and_set(STORAGE_PREFIX, key, old_value, new_value)
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

/// Information about the local node's network state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct NetworkState {
	peer_id: PeerId,
	external_addresses: Vec<Multiaddr>,
}

impl NetworkState {
	fn new(peer_id: PeerId, external_addresses: Vec<Multiaddr>) -> Self {
		NetworkState {
			peer_id,
			external_addresses,
		}
	}
}

impl From<NetworkState> for OpaqueNetworkState {
	fn from(state: NetworkState) -> OpaqueNetworkState {
		let enc = Encode::encode(&state.peer_id.into_bytes());
		let peer_id = OpaquePeerId::new(enc);

		let external_addresses: Vec<OpaqueMultiaddr> = state
			.external_addresses
			.iter()
			.map(|multiaddr| {
				let e = Encode::encode(&multiaddr.to_string());
				OpaqueMultiaddr::new(e)
			})
			.collect();

		OpaqueNetworkState {
			peer_id,
			external_addresses,
		}
	}
}

impl TryFrom<OpaqueNetworkState> for NetworkState {
	type Error = ();

	fn try_from(state: OpaqueNetworkState) -> Result<Self, Self::Error> {
		let inner_vec = state.peer_id.0;

		let bytes: Vec<u8> = Decode::decode(&mut &inner_vec[..]).ok_or(())?;
		let peer_id = PeerId::from_bytes(bytes).map_err(|_| ())?;

		let external_addresses: Result<Vec<Multiaddr>, Self::Error> = state.external_addresses
			.iter()
			.map(|enc_multiaddr| -> Result<Multiaddr, Self::Error> {
				let inner_vec = &enc_multiaddr.0;
				let bytes = <Vec<u8>>::decode(&mut &inner_vec[..]).ok_or(())?;
				let multiaddr_str = String::from_utf8(bytes).map_err(|_| ())?;
				let multiaddr = Multiaddr::from_str(&multiaddr_str).map_err(|_| ())?;
				Ok(multiaddr)
			})
			.collect();
		let external_addresses = external_addresses?;

		Ok(NetworkState {
			peer_id,
			external_addresses,
		})
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
	pub fn new<S: OffchainStorage, P: AuthorityKeyProvider<A::Block>>(
		transaction_pool: Arc<Pool<A>>,
		db: S,
		keys_password: Protected<String>,
		key_provider: P,
		at: BlockId<A::Block>,
		network_state: Arc<dyn NetworkStateInfo + Send + Sync>,
	) -> (Api<S, P, A::Block>, AsyncApi<A>) {
		let (sender, rx) = mpsc::unbounded();

		let api = Api {
			sender,
			db,
			keys_password,
			key_provider,
			network_state,
			at,
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
	use std::convert::TryFrom;
	use sr_primitives::traits::Zero;
	use client_db::offchain::LocalStorage;
	use crate::tests::TestProvider;
	use network::PeerId;
	use test_client::runtime::Block;

	struct MockNetworkStateInfo();

	impl NetworkStateInfo for MockNetworkStateInfo {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn peer_id(&self) -> PeerId {
			PeerId::random()
		}
	}

	fn offchain_api() -> (Api<LocalStorage, TestProvider<Block>, Block>, AsyncApi<impl ChainApi>) {
		let _ = env_logger::try_init();
		let db = LocalStorage::new_test();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(
			Pool::new(Default::default(), transaction_pool::ChainApi::new(client.clone()))
		);

		let mock = Arc::new(MockNetworkStateInfo());
		AsyncApi::new(pool, db, "pass".to_owned().into(), TestProvider::default(), BlockId::Number(Zero::zero()), mock)
	}

	#[test]
	fn should_get_timestamp() {
		let mut api = offchain_api().0;

		// Get timestamp from std.
		let now = SystemTime::now();
		let d: u64 = now.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_millis().try_into().unwrap();

		// Get timestamp from offchain api.
		let timestamp = api.timestamp();

		// Compare.
		assert!(timestamp.unix_millis() > 0);
		assert_eq!(timestamp.unix_millis(), d);
	}

	#[test]
	fn should_sleep() {
		let mut api = offchain_api().0;

		// Arrange.
		let now = api.timestamp();
		let delta = primitives::offchain::Duration::from_millis(100);
		let deadline = now.add(delta);

		// Act.
		api.sleep_until(deadline);
		let new_now = api.timestamp();

		// Assert.
		// The diff could be more than the sleep duration.
		assert!(new_now.unix_millis() - 100 >= now.unix_millis());
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
		assert_eq!(api.local_storage_compare_and_set(kind, key, Some(b"val"), b"xxx"), false);
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));

		// when
		assert_eq!(api.local_storage_compare_and_set(kind, key, Some(b"value"), b"xxx"), true);
		assert_eq!(api.local_storage_get(kind, key), Some(b"xxx".to_vec()));
	}

	#[test]
	fn should_compare_and_set_local_storage_with_none() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";

		// when
		let res = api.local_storage_compare_and_set(kind, key, None, b"value");

		// then
		assert_eq!(res, true);
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));
	}

	#[test]
	fn should_create_a_new_key_and_sign_and_verify_stuff() {
		let test = |kind: CryptoKind| {
			// given
			let mut api = offchain_api().0;
			let msg = b"Hello world!";

			// when
			let key = api.new_crypto_key(kind).unwrap();
			let signature = api.sign(key, msg).unwrap();

			// then
			let res = api.verify(key, msg, &signature).unwrap();
			assert_eq!(res, true);
			let res = api.verify(key, msg, &[]).unwrap();
			assert_eq!(res, false);
			let res = api.verify(key, b"Different msg", &signature).unwrap();
			assert_eq!(res, false);
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

		// when
		let signature = api.sign(CryptoKey::AuthorityKey, msg).unwrap();

		// then
		let res = api.verify(CryptoKey::AuthorityKey, msg, &signature).unwrap();
		assert_eq!(res, true);
		let res = api.verify(CryptoKey::AuthorityKey, msg, &[]).unwrap();
		assert_eq!(res, false);
		let res = api.verify(CryptoKey::AuthorityKey, b"Different msg", &signature).unwrap();
		assert_eq!(res, false);
	}

	#[test]
	fn should_convert_network_states() {
		// given
		let state = NetworkState::new(
			PeerId::random(),
			vec![
				Multiaddr::try_from("/ip4/127.0.0.1/tcp/1234".to_string()).unwrap(),
				Multiaddr::try_from("/ip6/2601:9:4f81:9700:803e:ca65:66e8:c21").unwrap(),
			],
		);

		// when
		let opaque_state = OpaqueNetworkState::from(state.clone());
		let converted_back_state = NetworkState::try_from(opaque_state).unwrap();

		// then
		assert_eq!(state, converted_back_state);
	}
}
